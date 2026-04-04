# coding: utf-8
from __future__ import print_function, unicode_literals

import base64
import errno
import os
import re
import select
import socket
import stat
import time
import xml.etree.ElementTree as ET

from .__init__ import TYPE_CHECKING
from .authsrv import LEELOO_DALLAS
from .multicast import MC_Sck, MCast
from .util import CachedSet, formatdate, html_escape, min_ex

if TYPE_CHECKING:
    from .broker_util import BrokerCli
    from .httpcli import HttpCli
    from .svchub import SvcHub

if True:  # pylint: disable=using-constant-test
    from typing import Optional, Union


GRP = "239.255.255.250"

# common DLNA protocol info for media types (with DLNA.ORG_PN and OP flags)
DLNA_PROTOCOL_INFO = {
    ".mp4": "http-get:*:video/mp4:DLNA.ORG_PN=AVC_MP4_MP_SD;DLNA.ORG_OP=01;DLNA.ORG_CI=0;DLNA.ORG_FLAGS=01700000000000000000000000000000",
    ".m4v": "http-get:*:video/mp4:DLNA.ORG_PN=AVC_MP4_MP_SD;DLNA.ORG_OP=01;DLNA.ORG_CI=0;DLNA.ORG_FLAGS=01700000000000000000000000000000",
    ".mkv": "http-get:*:video/x-matroska:DLNA.ORG_PN=MATROSKA;DLNA.ORG_OP=01;DLNA.ORG_CI=0;DLNA.ORG_FLAGS=01700000000000000000000000000000",
    ".webm": "http-get:*:video/x-matroska:DLNA.ORG_PN=MATROSKA;DLNA.ORG_OP=01;DLNA.ORG_CI=0;DLNA.ORG_FLAGS=01700000000000000000000000000000",
    ".avi": "http-get:*:video/x-msvideo:*",
    ".wmv": "http-get:*:video/x-ms-wmv:*",
    ".mp3": "http-get:*:audio/mpeg:DLNA.ORG_PN=MP3;DLNA.ORG_OP=01",
    ".flac": "http-get:*:audio/flac:*",
    ".wav": "http-get:*:audio/wav:*",
    ".ogg": "http-get:*:audio/ogg:*",
    ".aac": "http-get:*:audio/mp4:DLNA.ORG_PN=AAC_ISO_320;DLNA.ORG_OP=01",
    ".m4a": "http-get:*:audio/mp4:DLNA.ORG_PN=AAC_ISO_320;DLNA.ORG_OP=01",
    ".jpg": "http-get:*:image/jpeg:DLNA.ORG_PN=JPEG_SM;DLNA.ORG_OP=01",
    ".jpeg": "http-get:*:image/jpeg:DLNA.ORG_PN=JPEG_SM;DLNA.ORG_OP=01",
    ".png": "http-get:*:image/png:DLNA.ORG_PN=PNG_LRG;DLNA.ORG_OP=01",
}

CONTAINER_MIME = "object.container.storageFolder"
VIDEO_MIME = "object.item.videoItem"
AUDIO_MIME = "object.item.audioItem.musicTrack"
IMAGE_MIME = "object.item.imageItem.photo"


def _esc_xml(s):
    """Escape XML special characters."""
    return (
        s.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
        .replace("'", "&apos;")
    )


def _oid_encode(vpath):
    """Encode a copyparty vpath into a DLNA ObjectID."""
    if not vpath:
        return "0"
    return base64.urlsafe_b64encode(vpath.encode("utf-8")).decode("ascii").rstrip("=")


def _oid_decode(oid):
    """Decode a DLNA ObjectID back to a copyparty vpath."""
    if oid == "0":
        return ""
    # re-add padding
    padded = oid + "=" * (4 - len(oid) % 4) if len(oid) % 4 else oid
    return base64.urlsafe_b64decode(padded).decode("utf-8", errors="replace")


def _mime_for_ext(ext):
    """Return DLNA protocol info string for a file extension."""
    return DLNA_PROTOCOL_INFO.get(ext.lower(), "http-get:*:application/octet-stream:*")


def _dlna_class_for_ext(ext):
    """Return UPnP class for a file extension."""
    ext = ext.lower()
    if ext in (".mp4", ".mkv", ".avi", ".wmv", ".webm", ".mov", ".ts", ".mpg", ".mpeg"):
        return VIDEO_MIME
    if ext in (".mp3", ".flac", ".wav", ".ogg", ".aac", ".m4a", ".wma"):
        return AUDIO_MIME
    if ext in (".jpg", ".jpeg", ".png", ".gif", ".bmp", ".webp"):
        return IMAGE_MIME
    return "object.item"


def _dlna_res_flags(ext):
    """Return DLNA.ORG_FLAGS for a media type."""
    ext = ext.lower()
    if ext in (".jpg", ".jpeg", ".png", ".gif", ".bmp", ".webp"):
        return "0080000000000000"
    return "0100000000000000"


class SSDP_Sck(MC_Sck):
    def __init__(self, *a):
        super(SSDP_Sck, self).__init__(*a)
        self.hport = 0


class SSDPr(object):
    """generates http responses for httpcli"""

    def __init__(self, broker: "BrokerCli") -> None:
        self.broker = broker
        self.args = broker.args
        self._update_id = 0

    def reply(self, hc: "HttpCli") -> bool:
        if hc.vpath.endswith("device.xml"):
            return self.tx_device(hc)

        if hc.vpath.endswith("ContentDir.xml"):
            return self.tx_contentdir_scpd(hc)

        if hc.vpath.endswith("ConnectionMgr.xml"):
            return self.tx_connmgr_scpd(hc)

        if "/ctl/ContentDir" in hc.vpath:
            return self.tx_contentdir_ctl(hc)

        if "/ctl/ConnectionMgr" in hc.vpath:
            return self.tx_connmgr_ctl(hc)

        if "/ctl/" in hc.vpath:
            return self.tx_soap_fault(hc, 401, "Invalid Action")

        hc.reply(b"unknown request", 400)
        return False

    def _get_proto(self):
        return "https" if self.args.https_only else "http"

    def _get_base_url(self, hc):
        """Get http://ip:port base URL."""
        sip, sport = hc.s.getsockname()[:2]
        sip = sip.replace("::ffff:", "")
        return "{}://{}:{}".format(self._get_proto(), sip, sport)

    # ---------------------------------------------------------------
    # device description
    # ---------------------------------------------------------------
    def tx_device(self, hc: "HttpCli") -> bool:
        zs = """<?xml version="1.0"?>
<root xmlns="urn:schemas-upnp-org:device-1-0" xmlns:dlna="urn:schemas-dlna-org:device-1-0">
    <specVersion>
        <major>1</major>
        <minor>0</minor>
    </specVersion>
    <URLBase>{}</URLBase>
    <device>
        <deviceType>urn:schemas-upnp-org:device:MediaServer:1</deviceType>
        <friendlyName>{}</friendlyName>
        <manufacturer>ed</manufacturer>
        <manufacturerURL>https://ocv.me/</manufacturerURL>
        <modelDescription>copyparty DLNA media server</modelDescription>
        <modelName>copyparty</modelName>
        <modelNumber>1.0</modelNumber>
        <modelURL>https://github.com/9001/copyparty/</modelURL>
        <UDN>{}</UDN>
        <dlna:X_DLNADOC>DMS-1.50</dlna:X_DLNADOC>
        <presentationURL>{}</presentationURL>
        <serviceList>
            <service>
                <serviceType>urn:schemas-upnp-org:service:ContentDirectory:1</serviceType>
                <serviceId>urn:upnp-org:serviceId:ContentDirectory</serviceId>
                <controlURL>/.cpr/ssdp/ctl/ContentDir</controlURL>
                <eventSubURL>/.cpr/ssdp/evt/ContentDir</eventSubURL>
                <SCPDURL>/.cpr/ssdp/ContentDir.xml</SCPDURL>
            </service>
            <service>
                <serviceType>urn:schemas-upnp-org:service:ConnectionManager:1</serviceType>
                <serviceId>urn:upnp-org:serviceId:ConnectionManager</serviceId>
                <controlURL>/.cpr/ssdp/ctl/ConnectionMgr</controlURL>
                <eventSubURL>/.cpr/ssdp/evt/ConnectionMgr</eventSubURL>
                <SCPDURL>/.cpr/ssdp/ConnectionMgr.xml</SCPDURL>
            </service>
        </serviceList>
    </device>
</root>"""

        c = html_escape
        ubase = self._get_base_url(hc)
        zsl = self.args.zsl
        url = zsl if "://" in zsl else ubase + "/" + zsl.lstrip("/")
        name = self.args.doctitle
        zs = zs.strip().format(c(ubase), c(name), c(self.args.zsid), c(url))
        hc.reply(zs.encode("utf-8", "replace"))
        return False

    # ---------------------------------------------------------------
    # SCPD descriptions
    # ---------------------------------------------------------------
    def tx_contentdir_scpd(self, hc: "HttpCli") -> bool:
        zs = """<?xml version="1.0"?>
<scpd xmlns="urn:schemas-upnp-org:service-1-0">
    <specVersion><major>1</major><minor>0</minor></specVersion>
    <actionList>
        <action>
            <name>Browse</name>
            <argumentList>
                <argument><name>ObjectID</name><direction>in</direction><relatedStateVariable>A_ARG_TYPE_ObjectID</relatedStateVariable></argument>
                <argument><name>BrowseFlag</name><direction>in</direction><relatedStateVariable>A_ARG_TYPE_BrowseFlag</relatedStateVariable></argument>
                <argument><name>Filter</name><direction>in</direction><relatedStateVariable>A_ARG_TYPE_Filter</relatedStateVariable></argument>
                <argument><name>StartingIndex</name><direction>in</direction><relatedStateVariable>A_ARG_TYPE_Index</relatedStateVariable></argument>
                <argument><name>RequestedCount</name><direction>in</direction><relatedStateVariable>A_ARG_TYPE_Count</relatedStateVariable></argument>
                <argument><name>SortCriteria</name><direction>in</direction><relatedStateVariable>A_ARG_TYPE_SortCriteria</relatedStateVariable></argument>
                <argument><name>Result</name><direction>out</direction><relatedStateVariable>A_ARG_TYPE_Result</relatedStateVariable></argument>
                <argument><name>NumberReturned</name><direction>out</direction><relatedStateVariable>A_ARG_TYPE_Count</relatedStateVariable></argument>
                <argument><name>TotalMatches</name><direction>out</direction><relatedStateVariable>A_ARG_TYPE_Count</relatedStateVariable></argument>
                <argument><name>UpdateID</name><direction>out</direction><relatedStateVariable>A_ARG_TYPE_UpdateID</relatedStateVariable></argument>
            </argumentList>
        </action>
        <action>
            <name>GetSystemUpdateID</name>
            <argumentList>
                <argument><name>Id</name><direction>out</direction><relatedStateVariable>SystemUpdateID</relatedStateVariable></argument>
            </argumentList>
        </action>
        <action>
            <name>GetSortCapabilities</name>
            <argumentList>
                <argument><name>SortCaps</name><direction>out</direction><relatedStateVariable>SortCapabilities</relatedStateVariable></argument>
            </argumentList>
        </action>
        <action>
            <name>GetSearchCapabilities</name>
            <argumentList>
                <argument><name>SearchCaps</name><direction>out</direction><relatedStateVariable>SearchCapabilities</relatedStateVariable></argument>
            </argumentList>
        </action>
    </actionList>
    <serviceStateTable>
        <stateVariable sendEvents="yes"><name>SystemUpdateID</name><dataType>ui4</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>SortCapabilities</name><dataType>string</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>SearchCapabilities</name><dataType>string</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_ObjectID</name><dataType>string</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_BrowseFlag</name><dataType>string</dataType><allowedValueList><allowedValue>BrowseMetadata</allowedValue><allowedValue>BrowseDirectChildren</allowedValue></allowedValueList></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_Filter</name><dataType>string</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_Index</name><dataType>ui4</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_Count</name><dataType>ui4</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_SortCriteria</name><dataType>string</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_Result</name><dataType>string</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_UpdateID</name><dataType>ui4</dataType></stateVariable>
    </serviceStateTable>
</scpd>"""

        hc.reply(zs.encode("utf-8", "replace"))
        return False

    def tx_connmgr_scpd(self, hc: "HttpCli") -> bool:
        zs = """<?xml version="1.0"?>
<scpd xmlns="urn:schemas-upnp-org:service-1-0">
    <specVersion><major>1</major><minor>0</minor></specVersion>
    <actionList>
        <action>
            <name>GetProtocolInfo</name>
            <argumentList>
                <argument><name>Source</name><direction>out</direction><relatedStateVariable>A_ARG_TYPE_ProtocolInfo</relatedStateVariable></argument>
                <argument><name>Sink</name><direction>out</direction><relatedStateVariable>A_ARG_TYPE_ProtocolInfo</relatedStateVariable></argument>
            </argumentList>
        </action>
        <action>
            <name>GetCurrentConnectionIDs</name>
            <argumentList>
                <argument><name>ConnectionIDs</name><direction>out</direction><relatedStateVariable>A_ARG_TYPE_ConnectionIDs</relatedStateVariable></argument>
            </argumentList>
        </action>
        <action>
            <name>GetCurrentConnectionInfo</name>
            <argumentList>
                <argument><name>ConnectionID</name><direction>in</direction><relatedStateVariable>A_ARG_TYPE_ConnectionID</relatedStateVariable></argument>
                <argument><name>RcsID</name><direction>out</direction><relatedStateVariable>A_ARG_TYPE_RcsID</relatedStateVariable></argument>
                <argument><name>AVTransportID</name><direction>out</direction><relatedStateVariable>A_ARG_TYPE_AVTransportID</relatedStateVariable></argument>
                <argument><name>ProtocolInfo</name><direction>out</direction><relatedStateVariable>A_ARG_TYPE_ProtocolInfo</relatedStateVariable></argument>
                <argument><name>PeerConnectionManager</name><direction>out</direction><relatedStateVariable>A_ARG_TYPE_ConnectionManager</relatedStateVariable></argument>
                <argument><name>PeerConnectionID</name><direction>out</direction><relatedStateVariable>A_ARG_TYPE_ConnectionID</relatedStateVariable></argument>
                <argument><name>Direction</name><direction>out</direction><relatedStateVariable>A_ARG_TYPE_Direction</relatedStateVariable></argument>
                <argument><name>Status</name><direction>out</direction><relatedStateVariable>A_ARG_TYPE_ConnectionStatus</relatedStateVariable></argument>
            </argumentList>
        </action>
    </actionList>
    <serviceStateTable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_ProtocolInfo</name><dataType>string</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_ConnectionIDs</name><dataType>string</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_ConnectionID</name><dataType>i4</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_RcsID</name><dataType>i4</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_AVTransportID</name><dataType>i4</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_ConnectionManager</name><dataType>string</dataType></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_Direction</name><dataType>string</dataType><allowedValueList><allowedValue>Input</allowedValue><allowedValue>Output</allowedValue></allowedValueList></stateVariable>
        <stateVariable sendEvents="no"><name>A_ARG_TYPE_ConnectionStatus</name><dataType>string</dataType><allowedValueList><allowedValue>OK</allowedValue><allowedValue>ContentFormatMismatch</allowedValue><allowedValue>InsufficientBandwidth</allowedValue><allowedValue>UnreliableChannel</allowedValue><allowedValue>Unknown</allowedValue></allowedValueList></stateVariable>
        <stateVariable sendEvents="yes"><name>SourceProtocolInfo</name><dataType>string</dataType></stateVariable>
        <stateVariable sendEvents="yes"><name>SinkProtocolInfo</name><dataType>string</dataType></stateVariable>
    </serviceStateTable>
</scpd>"""

        hc.reply(zs.encode("utf-8", "replace"))
        return False

    # ---------------------------------------------------------------
    # SOAP helpers
    # ---------------------------------------------------------------
    def _read_soap_body(self, hc):
        """Read the SOAP XML body from the HTTP request."""
        try:
            clen = int(hc.headers.get("content-length", 0))
            if clen <= 0 or clen > 1_000_000:
                return None
            data = b""
            while len(data) < clen:
                chunk = hc.sr.recv(min(clen - len(data), 65536))
                if not chunk:
                    break
                data += chunk
            return data
        except Exception:
            return None

    def _parse_soap_action(self, body_bytes):
        """Parse SOAP XML body and return (service_type, action_name, params_dict)."""
        try:
            root = ET.fromstring(body_bytes)
        except ET.ParseError:
            return None, None, {}

        # find the first element in Body
        ns_soap = "http://schemas.xmlsoap.org/soap/envelope/"
        body = root.find(f"{{{ns_soap}}}Body")
        if body is None:
            return None, None, {}

        action_elem = None
        for child in body:
            action_elem = child
            break

        if action_elem is None:
            return None, None, {}

        # extract service type from namespace of the action element
        service_type = ""
        tag = action_elem.tag
        if "{" in tag:
            service_type = tag.split("}")[0].lstrip("{")

        # action name is the local part
        action_name = tag.split("}")[-1] if "}" in tag else tag

        # extract parameters
        params = {}
        for param in action_elem:
            local_name = param.tag.split("}")[-1] if "}" in param.tag else param.tag
            params[local_name] = param.text or ""

        return service_type, action_name, params

    def _soap_response(self, service_type, action_name, body_xml):
        """Wrap body_xml in a SOAP envelope response."""
        return (
            '<?xml version="1.0"?>\n'
            '<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" '
            's:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">\n'
            "  <s:Body>\n"
            "    <u:{0}Response xmlns:u=\"{1}\">\n"
            "      {2}\n"
            "    </u:{0}Response>\n"
            "  </s:Body>\n"
            "</s:Envelope>"
        ).format(action_name, service_type, body_xml)

    def _soap_fault(self, code, desc):
        """Generate a SOAP fault response."""
        return (
            '<?xml version="1.0"?>\n'
            '<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" '
            's:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">\n'
            "  <s:Body>\n"
            "    <s:Fault>\n"
            "      <faultcode>s:Client</faultcode>\n"
            "      <faultstring>UPnPError</faultstring>\n"
            "      <detail>\n"
            '        <UPnPError xmlns="urn:schemas-upnp-org:control-1-0">\n'
            "          <errorCode>{}</errorCode>\n"
            "          <errorDescription>{}</errorDescription>\n"
            "        </UPnPError>\n"
            "      </detail>\n"
            "    </s:Fault>\n"
            "  </s:Body>\n"
            "</s:Envelope>"
        ).format(code, desc)

    def _reply_soap(self, hc, xml_str, status=200):
        """Send a SOAP XML response."""
        body = xml_str.encode("utf-8", "replace")
        hc.reply(body, status, "text/xml; charset=utf-8", {"EXT": ""})
        return False

    def tx_soap_fault(self, hc, code=401, desc="Invalid Action"):
        return self._reply_soap(hc, self._soap_fault(code, desc), 500)

    # ---------------------------------------------------------------
    # ConnectionManager control
    # ---------------------------------------------------------------
    def tx_connmgr_ctl(self, hc: "HttpCli") -> bool:
        soap_body = self._read_soap_body(hc)
        if not soap_body:
            return self.tx_soap_fault(hc, 401, "Invalid Action")

        _, action, params = self._parse_soap_action(soap_body)

        svc = "urn:schemas-upnp-org:service:ConnectionManager:1"

        if action == "GetProtocolInfo":
            # advertise we can serve common media types
            sources = []
            for ext, info in DLNA_PROTOCOL_INFO.items():
                sources.append(info)
            # also advertise generic octet-stream
            sources.append("http-get:*:application/octet-stream:*")
            resp_body = (
                "<Source>{}</Source>\n"
                "    <Sink></Sink>"
            ).format(",".join(sources))
            resp = self._soap_response(svc, action, resp_body)
            return self._reply_soap(hc, resp)

        if action == "GetCurrentConnectionIDs":
            resp_body = "<ConnectionIDs></ConnectionIDs>"
            resp = self._soap_response(svc, action, resp_body)
            return self._reply_soap(hc, resp)

        if action == "GetCurrentConnectionInfo":
            resp_body = (
                "<RcsID>0</RcsID>\n"
                "    <AVTransportID>0</AVTransportID>\n"
                "    <ProtocolInfo></ProtocolInfo>\n"
                "    <PeerConnectionManager></PeerConnectionManager>\n"
                "    <PeerConnectionID>-1</PeerConnectionID>\n"
                "    <Direction>Output</Direction>\n"
                "    <Status>Unknown</Status>"
            )
            resp = self._soap_response(svc, action, resp_body)
            return self._reply_soap(hc, resp)

        return self.tx_soap_fault(hc, 401, "Invalid Action")

    # ---------------------------------------------------------------
    # ContentDirectory control
    # ---------------------------------------------------------------
    def tx_contentdir_ctl(self, hc: "HttpCli") -> bool:
        soap_body = self._read_soap_body(hc)
        if not soap_body:
            return self.tx_soap_fault(hc, 401, "Invalid Action")

        _, action, params = self._parse_soap_action(soap_body)

        svc = "urn:schemas-upnp-org:service:ContentDirectory:1"

        if action == "GetSystemUpdateID":
            resp_body = "<Id>{}</Id>".format(self._update_id)
            resp = self._soap_response(svc, action, resp_body)
            return self._reply_soap(hc, resp)

        if action == "GetSortCapabilities":
            resp_body = "<SortCaps></SortCaps>"
            resp = self._soap_response(svc, action, resp_body)
            return self._reply_soap(hc, resp)

        if action == "GetSearchCapabilities":
            resp_body = "<SearchCaps></SearchCaps>"
            resp = self._soap_response(svc, action, resp_body)
            return self._reply_soap(hc, resp)

        if action == "Browse":
            return self._handle_browse(hc, svc, params)

        return self.tx_soap_fault(hc, 401, "Invalid Action")

    def _handle_browse(self, hc, svc, params):
        """Handle ContentDirectory Browse action."""
        object_id = params.get("ObjectID", "0")
        browse_flag = params.get("BrowseFlag", "BrowseDirectChildren")
        start = int(params.get("StartingIndex", "0"))
        count = int(params.get("RequestedCount", "0"))

        vpath = _oid_decode(object_id)
        ubase = self._get_base_url(hc)

        try:
            vfs, rem = self.broker.asrv.vfs.get(vpath, LEELOO_DALLAS, True, False)
        except Exception as ex:
            return self._reply_soap(
                hc, self._soap_fault(701, "No such object"), 500
            )

        # collect directory entries
        containers = []  # (name, oid)
        items = []  # (name, oid, ext, size, mtime)

        try:
            abspath, real_entries, virt_vis = vfs._ls(rem, LEELOO_DALLAS, True, [[True]])
        except Exception:
            abspath, real_entries, virt_vis = "", [], {}

        # at root level, _ls won't list sub-volumes unless dk flag is set;
        # list them directly from the VFS nodes dict
        if not vpath:
            for name, vn in sorted(self.broker.asrv.vfs.nodes.items()):
                containers.append((name, _oid_encode(name)))

        # add virtual nodes from _ls (sub-volumes within a volume)
        for name, vn in sorted(virt_vis.items()):
            child_vp = vpath + "/" + name if vpath else name
            containers.append((name, _oid_encode(child_vp)))

        # add real directory entries
        for fname, st in real_entries:
            if fname.startswith("."):
                continue
            child_vp = vpath + "/" + fname if vpath else fname
            child_oid = _oid_encode(child_vp)

            if stat_is_dir(st):
                containers.append((fname, child_oid))
            else:
                ext = os.path.splitext(fname)[1]
                items.append((fname, child_oid, ext, st.st_size, int(st.st_mtime)))

        # build DIDL-Lite
        total = len(containers) + len(items)
        if count == 0:
            end = total
        else:
            end = min(start + count, total)

        all_entries = []
        for name, oid in containers:
            all_entries.append(("container", name, oid, CONTAINER_MIME, 0, 0))
        for name, oid, ext, size, mtime in items:
            all_entries.append(("item", name, oid, ext, size, mtime))

        page = all_entries[start:end]

        didl_parts = [
            '<?xml version="1.0"?>\n',
            '<DIDL-Lite xmlns="urn:schemas-upnp-org:metadata-1-0/DIDL-Lite/"',
            ' xmlns:dc="http://purl.org/dc/elements/1.1/"',
            ' xmlns:upnp="urn:schemas-upnp-org:metadata-1-0/upnp/"',
            ' xmlns:dlna="urn:schemas-dlna-org:metadata-1-0/">\n',
        ]

        for entry_type, name, oid, ext_or_class, size, mtime in page:
            esc_name = _esc_xml(name)
            if entry_type == "container":
                didl_parts.append(
                    '  <container id="{oid}" parentID="{pid}" restricted="1" childCount="0">\n'
                    '    <dc:title>{title}</dc:title>\n'
                    "    <upnp:class>{cls}</upnp:class>\n"
                    "  </container>\n".format(
                        oid=oid, pid=object_id, title=esc_name, cls=CONTAINER_MIME
                    )
                )
            else:
                # media item
                url = "{}/{}".format(ubase, vpath + "/" + name if vpath else name)
                # URL-encode spaces and special chars in the URL path
                url_parts = url.split("://", 1)
                if len(url_parts) == 2:
                    scheme, rest = url_parts
                    # encode each path segment
                    if "/" in rest:
                        host_port, path = rest.split("/", 1)
                        encoded_path = "/".join(
                            _url_quote(seg) for seg in path.split("/")
                        )
                        url = "{}://{}/{}".format(scheme, host_port, encoded_path)
                proto_info = _mime_for_ext(ext_or_class)
                upnp_class = _dlna_class_for_ext(ext_or_class)
                dlna_flags = _dlna_res_flags(ext_or_class)
                date_str = (
                    time.strftime("%Y-%m-%dT%H:%M:%S", time.gmtime(mtime))
                    if mtime
                    else ""
                )

                didl_parts.append(
                    '  <item id="{oid}" parentID="{pid}" restricted="1">\n'
                    '    <dc:title>{title}</dc:title>\n'
                    "    <upnp:class>{cls}</upnp:class>\n"
                    '{date}'
                    '    <res protocolInfo="{proto}"'
                    ' size="{size}">{url}</res>\n'
                    "  </item>\n".format(
                        oid=oid,
                        pid=object_id,
                        title=esc_name,
                        cls=upnp_class,
                        date=(
                            '    <dc:date>{}</dc:date>\n'.format(date_str)
                            if date_str
                            else ""
                        ),
                        proto=proto_info,
                        size=size,
                        url=_esc_xml(url),
                    )
                )

        didl_parts.append("</DIDL-Lite>")

        result_xml = "".join(didl_parts)

        resp_body = (
            "<Result>{result}</Result>\n"
            "    <NumberReturned>{ret}</NumberReturned>\n"
            "    <TotalMatches>{tot}</TotalMatches>\n"
            "    <UpdateID>{upd}</UpdateID>"
        ).format(
            result=_esc_xml(result_xml),
            ret=len(page),
            tot=total,
            upd=self._update_id,
        )

        resp = self._soap_response(svc, "Browse", resp_body)
        return self._reply_soap(hc, resp)


def _url_quote(s):
    """Percent-encode a URL path segment."""
    from urllib.parse import quote as _q

    return _q(s, safe="")


def stat_is_dir(st):
    """Check if a stat result is a directory."""
    return stat.S_ISDIR(st.st_mode)


class SSDPd(MCast):
    """communicates with ssdp clients over multicast"""

    def __init__(self, hub: "SvcHub", ngen: int) -> None:
        al = hub.args
        vinit = al.zsv and not al.zmv
        super(SSDPd, self).__init__(
            hub, SSDP_Sck, al.zs_on, al.zs_off, GRP, "", 1900, vinit
        )
        self.srv: dict[socket.socket, SSDP_Sck] = {}
        self.logsrc = "SSDP-{}".format(ngen)
        self.ngen = ngen

        self.rxc = CachedSet(0.7)
        self.txc = CachedSet(5)  # win10: every 3 sec
        self.ptn_st = re.compile(b"\nst: *upnp:rootdevice", re.I)

    def log(self, msg: str, c: Union[int, str] = 0) -> None:
        self.log_func(self.logsrc, msg, c)

    def run(self) -> None:
        try:
            bound = self.create_servers()
        except:
            t = "no server IP matches the ssdp config\n{}"
            self.log(t.format(min_ex()), 1)
            bound = []

        if not bound:
            self.log("failed to announce copyparty services on the network", 3)
            return

        # find http port for this listening ip
        for srv in self.srv.values():
            tcps = self.hub.tcpsrv.bound
            hp = next((x[1] for x in tcps if x[0] in ("0.0.0.0", srv.ip)), 0)
            hp = hp or next((x[1] for x in tcps if x[0] == "::"), 0)
            if not hp:
                hp = tcps[0][1]
                self.log("assuming port {} for {}".format(hp, srv.ip), 3)
            srv.hport = hp

        self.log("listening")
        try:
            self.run2()
        except OSError as ex:
            if ex.errno != errno.EBADF:
                raise

            self.log("stopping due to {}".format(ex), "90")

        self.log("stopped", 2)

    def run2(self) -> None:
        try:
            if self.args.no_poll:
                raise Exception()
            fd2sck = {}
            srvpoll = select.poll()
            for sck in self.srv:
                fd = sck.fileno()
                fd2sck[fd] = sck
                srvpoll.register(fd, select.POLLIN)
        except Exception as ex:
            srvpoll = None
            if not self.args.no_poll:
                t = "WARNING: failed to poll(), will use select() instead: %r"
                self.log(t % (ex,), 3)

        while self.running:
            if srvpoll:
                pr = srvpoll.poll((self.args.z_chk or 180) * 1000)
                rx = [fd2sck[x[0]] for x in pr if x[1] & select.POLLIN]
            else:
                rdy = select.select(self.srv, [], [], self.args.z_chk or 180)
                rx: list[socket.socket] = rdy[0]  # type: ignore

            self.rxc.cln()
            buf = b""
            addr = ("0", 0)
            for sck in rx:
                try:
                    buf, addr = sck.recvfrom(4096)
                    self.eat(buf, addr)
                except:
                    if not self.running:
                        break

                    t = "{} {} \033[33m|{}| {}\n{}".format(
                        self.srv[sck].name, addr, len(buf), repr(buf)[2:-1], min_ex()
                    )
                    self.log(t, 6)

    def stop(self) -> None:
        self.running = False
        for srv in self.srv.values():
            try:
                srv.sck.close()
            except:
                pass

        self.srv.clear()

    def eat(self, buf: bytes, addr: tuple[str, int]) -> None:
        cip = addr[0]
        if cip.startswith("169.254") and not self.ll_ok:
            return

        if buf in self.rxc.c:
            return

        srv: Optional[SSDP_Sck] = self.map_client(cip)  # type: ignore
        if not srv:
            return

        self.rxc.add(buf)
        if not buf.startswith(b"M-SEARCH * HTTP/1."):
            return

        if not self.ptn_st.search(buf):
            return

        if self.args.zsv:
            t = "{} [{}] \033[36m{} \033[0m|{}|"
            self.log(t.format(srv.name, srv.ip, cip, len(buf)), "90")

        zs = """
HTTP/1.1 200 OK
CACHE-CONTROL: max-age=1800
DATE: {0}
EXT:
LOCATION: http://{1}:{2}/.cpr/ssdp/device.xml
OPT: "http://schemas.upnp.org/upnp/1/0/"; ns=01
01-NLS: {3}
SERVER: UPnP/1.0 DLNADOC/1.50
ST: upnp:rootdevice
USN: {3}::upnp:rootdevice
BOOTID.UPNP.ORG: 0
CONFIGID.UPNP.ORG: 1

"""
        v4 = srv.ip.replace("::ffff:", "")
        zs = zs.format(formatdate(), v4, srv.hport, self.args.zsid)
        zb = zs[1:].replace("\n", "\r\n").encode("utf-8", "replace")
        srv.sck.sendto(zb, addr[:2])

        if cip not in self.txc.c:
            self.log("{} [{}] --> {}".format(srv.name, srv.ip, cip), 6)

        self.txc.add(cip)
        self.txc.cln()
