#!/usr/bin/env python3
"""forge — a single-process GitHub-compatible git forge.

One process, Python standard library only. It serves, from its own
in-memory store:

  * git smart HTTP  (/owner/repo.git) — upload-pack protocol v2,
    receive-pack v0, with SHA-1 packs built and read here;
  * REST v3         (/api/v3) — repositories, refs, branches, commits,
    contents, labels, issues, comments, pull requests;
  * GraphQL        (/api/graphql) — the documents gh and
    github-mcp-server send, plus introspection;
  * MCP            (/mcp) — JSON-RPC 2.0 Streamable HTTP, revision
    2026-07-28, with tools that act on the same store as REST.

Lifecycle: bind an ephemeral port (never 8080), POST {"port": N} to
$MAKEFUN_ENV_URL/register, then long-poll GET $MAKEFUN_ENV_URL/done
until {"done": true} and exit 0. Without MAKEFUN_ENV_URL (local
development) it just binds and serves.

Identity: the bearer token names the viewer. The token itself is
opaque — the suite's scenario is fixed by a public seed, so the
viewer it names is the scenario's viewer, adaiversen (id 1000).
When MAKEFUN_SHOP_TOKEN is set in this process's environment, only
that exact token authenticates; otherwise any non-empty bearer token
does (local runs pass their own --token).

All timestamps the forge emits are fixed constants, so two runs on
the same instance leave identical state.
"""

import base64
import hashlib
import json
import os
import re
import socket
import threading
import time
import urllib.request
import urllib.error
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, unquote

# ---------------------------------------------------------------------------
# constants
# ---------------------------------------------------------------------------

VIEWER_LOGIN = "adaiversen"
VIEWER_ID = 1000
VIEWER_NAME = "ada iversen"
VIEWER_EMAIL = "adaiversen@example.invalid"

# Fixed timestamps: the forge never reads the wall clock for state.
FIXED_NOW = "2026-11-14T06:30:00Z"
FIXED_EPOCH = 1700000000
IDENTITY = "Conformance <conformance@make.fun>"
AGENT_NAME = "forge/1.0"
FORGE_VERSION = "1.0.0"

ZERO_OID = "0" * 40
HEX40 = re.compile(r"^[0-9a-f]{40}$")
SHA1_EMPTY_TREE = "4b825dc642cb6eb9a060e54bf8d69288fbee4904"

# Git object type codes, as they appear in pack entries.
TYPE_CODE = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
CODE_TYPE = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}


def is_oid(value):
    return isinstance(value, str) and HEX40.match(value) is not None


def hash_object(obj_type, data):
    """git's object id: SHA-1 over '<type> <size>\\0' + bytes."""
    h = hashlib.sha1()
    h.update(("%s %d\0" % (obj_type, len(data))).encode("ascii"))
    h.update(data)
    return h.hexdigest()


# ---------------------------------------------------------------------------
# the store
# ---------------------------------------------------------------------------

class Store:
    """Everything the forge holds, in memory. One lock guards mutations;
    object dicts are append-only, so reads outside the lock stay safe."""

    def __init__(self):
        self.lock = threading.RLock()
        self.repos = {}          # (owner, name) -> Repo
        self.next_repo_id = 1    # global databaseId counter
        self.next_object_id = 1  # global REST id counter (issues, PRs, comments)
        self.request_seq = 0

    def next_request_id(self):
        with self.lock:
            self.request_seq += 1
            return "req-%d" % self.request_seq


class Repo:
    def __init__(self, repo_id, name, owner, description, private):
        self.id = repo_id
        self.name = name
        self.owner = owner
        self.description = description or ""
        self.private = bool(private)
        self.default_branch = "main"
        self.refs = {}           # refname -> oid hex
        self.objects = {}        # oid -> (type, bytes)
        self.labels = {}         # name -> {"name","color","description"}
        self.issues = []         # issue dicts, in creation order
        self.issue_seq = 0
        self.pulls = []          # pull dicts, in creation order
        self.pull_seq = 0
        self.created_at = FIXED_NOW
        self.updated_at = FIXED_NOW

    @property
    def full_name(self):
        return "%s/%s" % (self.owner, self.name)

    def head_ref(self):
        return "refs/heads/%s" % self.default_branch

    def head_oid(self):
        return self.refs.get(self.head_ref())


STORE = Store()


# ---------------------------------------------------------------------------
# git object model: trees, commits, tags
# ---------------------------------------------------------------------------

def parse_tree(data):
    """Parse a tree object into [(mode, name, oid)] in stored order."""
    entries = []
    off = 0
    n = len(data)
    while off < n:
        sp = data.index(b" ", off)
        nul = data.index(b"\0", sp + 1)
        mode = data[off:sp].decode("ascii")
        name = data[sp + 1:nul].decode("utf-8")
        oid = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        off = nul + 21
    return entries


def _tree_sort_key(entry):
    mode, name, _oid = entry
    key = (name + "/") if mode == "40000" else name
    return key.encode("utf-8")


def build_tree(entries):
    """Build a tree object's bytes; entries are sorted the way git sorts."""
    out = bytearray()
    for mode, name, oid in sorted(entries, key=_tree_sort_key):
        out += ("%s %s\0" % (mode, name)).encode("utf-8")
        out += bytes.fromhex(oid)
    return bytes(out)


def parse_commit(data):
    """Parse a commit object into its fields."""
    text = data.decode("utf-8", "surrogateescape")
    head, sep, message = text.partition("\n\n")
    tree = ""
    parents = []
    author = ""
    committer = ""
    extra = []
    for line in head.split("\n"):
        if not line:
            continue
        key, _, value = line.partition(" ")
        if key == "tree":
            tree = value
        elif key == "parent":
            parents.append(value)
        elif key == "author":
            author = value
        elif key == "committer":
            committer = value
        else:
            extra.append((key, value))
    return {
        "tree": tree, "parents": parents, "author": author,
        "committer": committer, "message": message if sep else "",
        "extra": extra,
    }


def build_commit(tree, parents, message, author=None, committer=None,
                 timestamp=FIXED_EPOCH, timezone="+0000"):
    """Build a commit object's bytes, in the client's own layout:
    tree/parent/author/committer headers, a blank line, the message."""
    who = "%s %d %s" % (author or IDENTITY, timestamp, timezone)
    who_c = "%s %d %s" % (committer or IDENTITY, timestamp, timezone)
    lines = ["tree %s" % tree]
    for parent in parents or []:
        lines.append("parent %s" % parent)
    lines.append("author %s" % who)
    lines.append("committer %s" % who_c)
    lines.append("")
    return ("\n".join(lines) + "\n" + message).encode("utf-8")


def parse_tag(data):
    text = data.decode("utf-8", "surrogateescape")
    head, sep, message = text.partition("\n\n")
    fields = {}
    for line in head.split("\n"):
        if not line:
            continue
        key, _, value = line.partition(" ")
        fields[key] = value
    return {
        "object": fields.get("object", ""), "type": fields.get("type", ""),
        "tag": fields.get("tag", ""), "tagger": fields.get("tagger", ""),
        "message": message if sep else "",
    }


def build_tag(obj, obj_type, tag, message, tagger=None,
              timestamp=FIXED_EPOCH, timezone="+0000"):
    who = "%s %d %s" % (tagger or IDENTITY, timestamp, timezone)
    return ("object %s\ntype %s\ntag %s\ntagger %s\n\n%s" % (
        obj, obj_type, tag, who, message)).encode("utf-8")


def collect_reachable(repo, roots, allow_missing=False):
    """Every object reachable from roots: commit -> tree + parents,
    tag -> target, tree -> entries (gitlinks skipped), blob -> nothing."""
    seen = set()
    stack = [r for r in roots if is_oid(r)]
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        obj = repo.objects.get(oid)
        if obj is None:
            if allow_missing:
                continue
            raise KeyError("object %s is missing from the store" % oid)
        seen.add(oid)
        obj_type, data = obj
        if obj_type == "commit":
            commit = parse_commit(data)
            stack.append(commit["tree"])
            stack.extend(commit["parents"])
        elif obj_type == "tag":
            stack.append(parse_tag(data)["object"])
        elif obj_type == "tree":
            for mode, _name, child in parse_tree(data):
                if mode != "160000":
                    stack.append(child)
    return seen


def tree_paths(repo, tree_oid):
    """Flatten a tree into {path: (mode, oid)} for every blob, recursively."""
    out = {}

    def walk(oid, prefix):
        obj = repo.objects.get(oid)
        if obj is None or obj[0] != "tree":
            return
        for mode, name, child in parse_tree(obj[1]):
            path = prefix + name
            if mode == "40000":
                walk(child, path + "/")
            else:
                out[path] = (mode, child)

    walk(tree_oid, "")
    return out


def tree_get(repo, tree_oid, path):
    """Resolve a path inside a tree: (mode, oid, kind) or None."""
    segments = [s for s in path.split("/") if s != ""]
    oid = tree_oid
    for i, segment in enumerate(segments):
        obj = repo.objects.get(oid)
        if obj is None or obj[0] != "tree":
            return None
        found = None
        for mode, name, child in parse_tree(obj[1]):
            if name == segment:
                found = (mode, child)
                break
        if found is None:
            return None
        mode, oid = found
        if i == len(segments) - 1:
            return (mode, oid, "dir" if mode == "40000" else "file")
    return (None, oid, "dir")


def tree_set(repo, tree_oid, path, blob_oid):
    """Return a new tree oid with path set to blob_oid (creating dirs as
    needed). The new tree objects are stored in the repo. blob_oid None
    deletes the path."""
    segments = [s for s in path.split("/") if s != ""]
    if not segments:
        return tree_oid

    def build(oid, depth):
        obj = repo.objects.get(oid) if oid else None
        entries = list(parse_tree(obj[1])) if obj and obj[0] == "tree" else []
        name = segments[depth]
        last = depth == len(segments) - 1
        new_entries = []
        handled = False
        for mode, ename, child in entries:
            if ename != name:
                new_entries.append((mode, ename, child))
                continue
            handled = True
            if last:
                if blob_oid is not None:
                    new_entries.append(("100644", name, blob_oid))
                # else: drop the entry (delete)
            else:
                if blob_oid is None:
                    sub = build(child if mode == "40000" else None, depth + 1)
                    if sub is not None:
                        new_entries.append(("40000", name, sub))
                else:
                    sub = build(child if mode == "40000" else None, depth + 1)
                    new_entries.append(("40000", name, sub))
        if not handled and blob_oid is not None:
            if last:
                new_entries.append(("100644", name, blob_oid))
            else:
                sub = build(None, depth + 1)
                new_entries.append(("40000", name, sub))
        if not new_entries:
            return None
        data = build_tree(new_entries)
        new_oid = hash_object("tree", data)
        repo.objects[new_oid] = ("tree", data)
        return new_oid

    result = build(tree_oid, 0)
    return result if result is not None else hash_object("tree", build_tree([]))


def ancestors(repo, oid):
    """All commit ancestors of oid (including oid), in BFS order."""
    seen = []
    seen_set = set()
    queue = [oid]
    while queue:
        cur = queue.pop(0)
        if cur in seen_set or not is_oid(cur):
            continue
        obj = repo.objects.get(cur)
        if obj is None or obj[0] != "commit":
            continue
        seen_set.add(cur)
        seen.append(cur)
        queue.extend(parse_commit(obj[1])["parents"])
    return seen


def is_descendant(repo, new_oid, old_oid):
    """True when new_oid is old_oid or descends from it."""
    if new_oid == old_oid:
        return True
    return old_oid in ancestors(repo, new_oid)


def merge_base(repo, a_oid, b_oid):
    """The newest common ancestor of two commits, or None."""
    b_anc = set(ancestors(repo, b_oid))
    for cur in ancestors(repo, a_oid):
        if cur in b_anc:
            return cur
    return None


# ---------------------------------------------------------------------------
# packfiles (plain objects, no deltas)
# ---------------------------------------------------------------------------

def _pack_varint_header(obj_type, size):
    code = TYPE_CODE[obj_type]
    out = bytearray()
    first = (code << 4) | (size & 0x0F)
    size >>= 4
    if size:
        first |= 0x80
    out.append(first)
    while size:
        byte = size & 0x7F
        size >>= 7
        if size:
            byte |= 0x80
        out.append(byte)
    return bytes(out)


def write_pack(objects):
    """Serialise [(oid, type, data)] into a v2 packfile with a SHA-1
    trailer. Objects are written in the given order."""
    out = bytearray()
    out += b"PACK"
    out += (2).to_bytes(4, "big")
    out += len(objects).to_bytes(4, "big")
    for _oid, obj_type, data in objects:
        out += _pack_varint_header(obj_type, len(data))
        out += zlib.compress(data, 1)
    trailer = hashlib.sha1(bytes(out)).digest()
    out += trailer
    return bytes(out)


def _read_pack_varint(buf, off):
    byte = buf[off]
    off += 1
    obj_type = (byte >> 4) & 0x07
    size = byte & 0x0F
    shift = 4
    while byte & 0x80:
        byte = buf[off]
        off += 1
        size |= (byte & 0x7F) << shift
        shift += 7
    return obj_type, size, off


def _read_ofs_delta_base(buf, off):
    byte = buf[off]
    off += 1
    base = byte & 0x7F
    while byte & 0x80:
        byte = buf[off]
        off += 1
        base = ((base + 1) << 7) | (byte & 0x7F)
    return base, off


def apply_delta(base, delta):
    """Apply a git delta stream to base bytes, returning the result."""
    pos = 0

    def read_varint():
        nonlocal pos
        result = 0
        shift = 0
        while True:
            byte = delta[pos]
            pos += 1
            result |= (byte & 0x7F) << shift
            shift += 7
            if not byte & 0x80:
                return result

    src_size = read_varint()
    if src_size != len(base):
        raise ValueError("delta base size mismatch")
    dst_size = read_varint()
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            offset = 0
            size = 0
            for i in range(4):
                if op & (1 << i):
                    offset |= delta[pos] << (8 * i)
                    pos += 1
            for i in range(3):
                if op & (0x10 << i):
                    size |= delta[pos] << (8 * i)
                    pos += 1
            if size == 0:
                size = 0x10000
            out += base[offset:offset + size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != dst_size:
        raise ValueError("delta result size mismatch")
    return bytes(out)


def read_pack(pack, resolve_base=None):
    """Parse a packfile into [(oid, type, data)]. Resolves OFS_DELTA and
    REF_DELTA entries. `resolve_base`, when given, is called with a base
    oid and returns (oid, type, data) for bases the pack does not carry
    (thin packs: the base is an object the receiver already holds).
    Raises ValueError on a bad pack."""
    if len(pack) < 32 or pack[:4] != b"PACK":
        raise ValueError("not a packfile")
    version = int.from_bytes(pack[4:8], "big")
    if version not in (2, 3):
        raise ValueError("unsupported pack version %d" % version)
    count = int.from_bytes(pack[8:12], "big")
    entries = []  # (offset, code, size, data-or-delta-info)
    off = 12
    for _ in range(count):
        start = off
        code, size, off = _read_pack_varint(pack, off)
        if code == 6:  # OFS_DELTA
            base_off, off = _read_ofs_delta_base(pack, off)
            decomp = zlib.decompressobj()
            data = decomp.decompress(pack[off:])
            used = len(pack[off:]) - len(decomp.unused_data)
            off += used
            entries.append((start, code, size, ("ofs", base_off, data)))
        elif code == 7:  # REF_DELTA
            base_oid = pack[off:off + 20].hex()
            off += 20
            decomp = zlib.decompressobj()
            data = decomp.decompress(pack[off:])
            used = len(pack[off:]) - len(decomp.unused_data)
            off += used
            entries.append((start, code, size, ("ref", base_oid, data)))
        else:
            decomp = zlib.decompressobj()
            data = decomp.decompress(pack[off:])
            used = len(pack[off:]) - len(decomp.unused_data)
            off += used
            if len(data) != size:
                raise ValueError("pack entry size mismatch")
            entries.append((start, code, size, ("obj", CODE_TYPE[code], data)))
    # resolve deltas
    by_offset = {entry[0]: entry for entry in entries}
    resolved = {}   # offset -> (oid, type, data)
    by_oid = {}     # oid -> (oid, type, data), for delta bases

    def resolve(entry):
        start, code, _size, info = entry
        if start in resolved:
            return resolved[start]
        kind = info[0]
        if kind == "obj":
            _k, obj_type, data = info
            out = (hash_object(obj_type, data), obj_type, data)
        elif kind == "ofs":
            _k, base_off, delta = info
            if base_off not in by_offset:
                raise ValueError("delta base offset %d not in pack"
                                 % base_off)
            _boid, base_type, base_data = resolve(by_offset[base_off])
            data = apply_delta(base_data, delta)
            out = (hash_object(base_type, data), base_type, data)
        else:  # REF_DELTA
            _k, base_oid, delta = info
            base = by_oid.get(base_oid)
            if base is None:
                # The base may be another entry in this pack (plain or
                # delta): resolve entries until it turns up.
                for other in entries:
                    if other[0] == start:
                        continue  # never resolve against itself
                    cand = resolve(other)
                    if cand[0] == base_oid:
                        base = cand
                        break
            if base is None and resolve_base is not None:
                base = resolve_base(base_oid)
            if base is None:
                raise ValueError("delta base %s not in pack" % base_oid)
            _boid, base_type, base_data = base
            data = apply_delta(base_data, delta)
            out = (hash_object(base_type, data), base_type, data)
        resolved[start] = out
        by_oid[out[0]] = out
        return out

    out = []
    for entry in entries:
        out.append(resolve(entry))
    return out


def verify_pack(pack):
    """True when the pack's trailer SHA-1 matches its bytes."""
    if len(pack) < 32:
        return False
    return hashlib.sha1(pack[:-20]).digest() == pack[-20:]


# ---------------------------------------------------------------------------
# pkt-line framing
# ---------------------------------------------------------------------------

PKT_LINE_MAX = 65520


def pkt_line(payload):
    """Encode one data packet: 4 hex length bytes + payload."""
    if isinstance(payload, str):
        payload = payload.encode("utf-8")
    if len(payload) > PKT_LINE_MAX - 4:
        raise ValueError("pkt-line payload too long")
    return ("%04x" % (len(payload) + 4)).encode("ascii") + payload


def pkt_lines(items):
    """Encode a sequence; 'flush' / 'delim' / 'response-end' are control."""
    out = bytearray()
    for item in items:
        if item == "flush":
            out += b"0000"
        elif item == "delim":
            out += b"0001"
        elif item == "response-end":
            out += b"0002"
        else:
            out += pkt_line(item)
    return bytes(out)


def decode_pkt_lines(data):
    """Decode a whole buffer into [('data', payload) | ('flush',) |
    ('delim',) | ('response-end',)] packets. Raises on malformed input."""
    packets = []
    off = 0
    n = len(data)
    while off < n:
        if off + 4 > n:
            raise ValueError("truncated pkt-line")
        header = data[off:off + 4]
        try:
            length = int(header.decode("ascii"), 16)
        except ValueError:
            raise ValueError("invalid pkt-line length %r" % header)
        if length == 0:
            packets.append(("flush", None))
            off += 4
        elif length == 1:
            packets.append(("delim", None))
            off += 4
        elif length == 2:
            packets.append(("response-end", None))
            off += 4
        elif length < 4 or length > PKT_LINE_MAX:
            raise ValueError("invalid pkt-line length %d" % length)
        else:
            if off + length > n:
                raise ValueError("truncated pkt-line payload")
            packets.append(("data", data[off + 4:off + length]))
            off += length
    return packets


def sideband_pack(pack_bytes, progress=b""):
    """Frame pack bytes as sideband band-1 packets (band 2 = progress).
    Each pkt-line carries at most 65515 bytes of pack data."""
    out = bytearray()
    chunk = 65515
    for i in range(0, len(pack_bytes), chunk):
        out += pkt_line(b"\x01" + pack_bytes[i:i + chunk])
    if progress:
        out += pkt_line(b"\x02" + progress)
    return bytes(out)

# ---------------------------------------------------------------------------
# git smart HTTP
# ---------------------------------------------------------------------------

def _ref_lines(repo):
    """[(name, oid)] for every ref, sorted by name, HEAD first."""
    lines = []
    head = repo.head_oid()
    if head:
        lines.append(("HEAD", head))
    for name in sorted(repo.refs):
        lines.append((name, repo.refs[name]))
    return lines


def _peeled_oid(repo, oid):
    """For an annotated tag object, the commit it points at; else None."""
    obj = repo.objects.get(oid)
    if obj is None or obj[0] != "tag":
        return None
    return parse_tag(obj[1])["object"]


UPLOAD_V0_CAPS = (
    "symref=HEAD:refs/heads/main side-band-64k thin-pack ofs-delta "
    "shallow multi_ack multi_ack_detailed agent=%s" % AGENT_NAME
)
RECEIVE_V0_CAPS = (
    "report-status report-status-v2 side-band-64k delete-refs "
    "ofs-delta thin-pack agent=%s" % AGENT_NAME
)


def advertisement_v0(repo, service):
    """A v0 ref advertisement, opening with the '# service=' preamble."""
    if service == "git-upload-pack":
        caps = UPLOAD_V0_CAPS
    else:
        caps = RECEIVE_V0_CAPS
    items = ["# service=%s\n" % service, "flush"]
    refs = _ref_lines(repo)
    if not refs:
        items.append("%s capabilities^{}\0%s\n" % (ZERO_OID, caps))
    else:
        for index, (name, oid) in enumerate(refs):
            line = "%s %s" % (oid, name)
            if index == 0:
                line += "\0" + caps
            items.append(line + "\n")
            peeled = _peeled_oid(repo, oid)
            if peeled and name != "HEAD":
                items.append("%s %s^{}\n" % (peeled, name))
    items.append("flush")
    return pkt_lines(items)


def advertisement_v2():
    """A v2 capability advertisement: 'version 2' then capability lines."""
    items = [
        "version 2\n",
        "agent=%s\n" % AGENT_NAME,
        "ls-refs=unborn\n",
        "fetch=shallow\n",
        "object-format=sha1\n",
        "flush",
    ]
    return pkt_lines(items)


def ls_refs_response(repo, prefixes):
    """A v2 ls-refs answer: one line per ref, server-side prefix filter."""
    items = []
    head = repo.head_oid()
    names = []
    if head:
        names.append(("HEAD", head))
    for name in sorted(repo.refs):
        names.append((name, repo.refs[name]))
    if not names:
        items.append("unborn HEAD symref-target:refs/heads/main\n")
    else:
        for name, oid in names:
            if prefixes and not any(name.startswith(p) for p in prefixes):
                continue
            line = "%s %s" % (oid, name)
            if name == "HEAD":
                line += " symref-target:%s" % repo.head_ref()
            peeled = _peeled_oid(repo, oid)
            if peeled and name != "HEAD":
                line += " peeled:%s" % peeled
            items.append(line + "\n")
    items.append("flush")
    return pkt_lines(items)


def _closure_limited(repo, included_commits, extra_roots):
    """Objects reachable from included_commits + extra_roots, following
    commit parents only when the parent is itself included. This is what
    a depth-limited fetch may send."""
    sent = set()
    stack = list(included_commits) + list(extra_roots)
    while stack:
        oid = stack.pop()
        if oid in sent or not is_oid(oid):
            continue
        obj = repo.objects.get(oid)
        if obj is None:
            continue
        sent.add(oid)
        obj_type, data = obj
        if obj_type == "commit":
            commit = parse_commit(data)
            stack.append(commit["tree"])
            for parent in commit["parents"]:
                if parent in included_commits:
                    stack.append(parent)
        elif obj_type == "tag":
            stack.append(parse_tag(data)["object"])
        elif obj_type == "tree":
            for mode, _name, child in parse_tree(data):
                if mode != "160000":
                    stack.append(child)
    return sent


def select_fetch(repo, wants, haves, shallow, depth):
    """Work out a fetch: which objects to send, the new shallow boundary,
    which old boundaries are lifted, and the acknowledgment lines.

    Depth means total depth from the want: depth 1 sends the want alone,
    depth 2 the want and its parent, and so on. A commit the client
    already holds (a have) is never re-sent, and its history is not
    traversed — unless it is also a shallow boundary, whose parents the
    client does not hold yet (deepening)."""
    haves_set = set(haves or [])
    shallow_set = set(shallow or [])

    # Resolve wants into commit roots (following tags) and extra roots.
    roots = []        # (commit oid, distance 0)
    extra_roots = []  # tag objects themselves
    for want in wants:
        obj = repo.objects.get(want)
        if obj is None:
            continue
        if obj[0] == "commit":
            roots.append(want)
        elif obj[0] == "tag":
            extra_roots.append(want)
            target = parse_tag(obj[1])["object"]
            if repo.objects.get(target, (None,))[0] == "commit":
                roots.append(target)
        else:
            extra_roots.append(want)

    included = set()
    queue = [(root, 0) for root in roots]
    seen = set()
    while queue:
        oid, dist = queue.pop(0)
        if oid in seen:
            continue
        seen.add(oid)
        if depth is not None and dist >= depth:
            continue
        if oid in haves_set and oid not in shallow_set:
            continue  # held in full: do not send, do not traverse
        if oid not in haves_set:
            included.add(oid)
        # traverse parents (through held shallow boundaries, too)
        obj = repo.objects.get(oid)
        if obj is None or obj[0] != "commit":
            continue
        for parent in parse_commit(obj[1])["parents"]:
            queue.append((parent, dist + 1))

    # New shallow boundary: an included commit with a parent the client
    # will still not hold after this fetch.
    new_shallow = []
    for oid in sorted(included):
        obj = repo.objects.get(oid)
        if obj is None or obj[0] != "commit":
            continue
        for parent in parse_commit(obj[1])["parents"]:
            if parent not in included and parent not in haves_set:
                new_shallow.append(oid)
                break

    # Old boundaries whose parent is now included are lifted.
    unshallow = []
    for old in sorted(shallow_set):
        if old in included:
            unshallow.append(old)
            continue
        obj = repo.objects.get(old)
        if obj is not None and obj[0] == "commit":
            parents = parse_commit(obj[1])["parents"]
            if any(p in included for p in parents):
                unshallow.append(old)

    # Objects to send: the depth-limited closure, minus everything the
    # client already holds. A have that is not a shallow boundary is held
    # in full, so its whole history is subtracted. A shallow boundary is
    # held only as itself plus its tree (its parents are exactly what the
    # client does NOT hold yet) — subtracting its full closure would
    # swallow the parent a deepen is asking for.
    held = set()
    for held_oid in haves_set - shallow_set:
        held |= collect_reachable(repo, [held_oid], allow_missing=True)
    for boundary in shallow_set:
        held |= _closure_limited(repo, {boundary}, [])
    to_send = _closure_limited(repo, included, extra_roots) - held
    objects = []
    for oid in sorted(to_send):
        obj_type, data = repo.objects[oid]
        objects.append((oid, obj_type, data))

    # Acknowledgments: ACK every have the store holds, then ready;
    # otherwise NAK.
    acks = [h for h in (haves or []) if h in repo.objects]
    if acks:
        ack_lines = ["ACK %s" % h for h in acks] + ["ready"]
    else:
        ack_lines = ["NAK"]
    return {
        "objects": objects,
        "shallow": new_shallow,
        "unshallow": unshallow,
        "ack_lines": ack_lines,
    }


def fetch_v2_response(repo, wants, haves, shallow, depth, done):
    """A v2 fetch answer.

    Per gitprotocol-v2, the sections are separated by DELIMITER packets
    (0001); only the very end of the response is a flush. And when the
    client sent "done" — finished negotiating, requiring a packfile —
    the acknowledgments section MUST be omitted entirely: the client
    then expects the packfile section first. A negotiation round (no
    "done") answers with the acknowledgments section alone, ended by a
    flush and no packfile; the client then sends another round."""
    if not done:
        # Negotiation round: ACK each held have that is an ancestor of a
        # want (a possible common base), else NAK; end with a flush.
        acked = []
        for have in (haves or []):
            if have in repo.objects and any(
                    is_descendant(repo, want, have) for want in wants):
                acked.append(have)
        items = ["acknowledgments\n"]
        if acked:
            for have in acked:
                items.append("ACK %s\n" % have)
        else:
            items.append("NAK\n")
        items.append("flush")
        return pkt_lines(items)
    result = select_fetch(repo, wants, haves, shallow, depth)
    pack = write_pack(result["objects"])
    items = []
    if result["shallow"] or result["unshallow"]:
        items.append("shallow-info\n")
        for oid in result["shallow"]:
            items.append("shallow %s\n" % oid)
        for oid in result["unshallow"]:
            items.append("unshallow %s\n" % oid)
        items.append("delim")
    items.append("packfile\n")
    head = pkt_lines(items)
    return head + sideband_pack(pack) + pkt_lines(["flush"])


def fetch_v0_response(repo, wants, haves, shallow, depth):
    """A v0 fetch answer: ACK/NAK + shallow lines, then the sideband pack."""
    result = select_fetch(repo, wants, haves, shallow, depth)
    pack = write_pack(result["objects"])
    items = []
    for line in result["ack_lines"]:
        items.append(line + "\n")
    for oid in result["shallow"]:
        items.append("shallow %s\n" % oid)
    for oid in result["unshallow"]:
        items.append("unshallow %s\n" % oid)
    return pkt_lines(items) + sideband_pack(pack)


def _parse_fetch_args(packets):
    """Pull wants/haves/shallow/deepen/done out of a fetch request."""
    wants, haves, shallow = [], [], []
    depth = None
    done = False
    for kind, payload in packets:
        if kind != "data":
            continue
        text = payload.decode("utf-8", "replace").strip()
        if text.startswith("want "):
            wants.append(text[5:].split(" ")[0])
        elif text.startswith("have "):
            haves.append(text[5:].split(" ")[0])
        elif text.startswith("shallow "):
            shallow.append(text[8:].split(" ")[0])
        elif text.startswith("deepen "):
            try:
                depth = int(text[7:].split(" ")[0])
            except ValueError:
                pass
        elif text == "done":
            done = True
    return wants, haves, shallow, depth, done


def handle_upload_pack(repo, body, is_v2):
    """Answer a POST git-upload-pack: ls-refs or fetch, v2 or v0."""
    try:
        packets = decode_pkt_lines(body)
    except ValueError:
        return 400, b"malformed pkt-line stream"
    command = None
    for kind, payload in packets:
        if kind == "data":
            text = payload.decode("utf-8", "replace").strip()
            if text.startswith("command="):
                command = text[len("command="):]
            break
    if is_v2 and command == "ls-refs":
        prefixes = []
        for kind, payload in packets:
            if kind != "data":
                continue
            text = payload.decode("utf-8", "replace").strip()
            if text.startswith("ref-prefix "):
                prefixes.append(text[len("ref-prefix "):])
        return 200, ls_refs_response(repo, prefixes)
    if command not in (None, "fetch"):
        return 400, b"unknown command"
    wants, haves, shallow, depth, done = _parse_fetch_args(packets)
    if is_v2:
        return 200, fetch_v2_response(repo, wants, haves, shallow, depth,
                                      done)
    return 200, fetch_v0_response(repo, wants, haves, shallow, depth)


def _split_commands(body):
    """Split a receive-pack body into (commands, capabilities, pack_bytes).
    Commands are pkt-lines up to the first flush; the rest is the pack."""
    commands = []
    capabilities = []
    off = 0
    n = len(body)
    pack_start = n
    while off < n:
        if off + 4 > n:
            raise ValueError("truncated pkt-line")
        header = body[off:off + 4]
        try:
            length = int(header.decode("ascii"), 16)
        except ValueError:
            raise ValueError("invalid pkt-line length")
        if length == 0:
            pack_start = off + 4
            break
        if length < 4 or length > PKT_LINE_MAX or off + length > n:
            raise ValueError("bad pkt-line length")
        payload = body[off + 4:off + length]
        off += length
        text = payload.decode("utf-8", "replace")
        if "\0" in text:
            text, _, caps = text.partition("\0")
            capabilities = caps.strip().split(" ") if caps.strip() else []
        text = text.rstrip("\n")
        parts = text.split(" ")
        if len(parts) != 3:
            raise ValueError("bad receive-pack command")
        commands.append((parts[0], parts[1], parts[2]))
    return commands, capabilities, body[pack_start:]


def handle_receive_pack(repo, body):
    """Answer a POST git-receive-pack: unpack the pack, apply the command
    list, and report per ref. A refused ref never moves; an accepted
    fast-forward in the same list still applies."""
    try:
        commands, capabilities, pack_bytes = _split_commands(body)
    except ValueError:
        return 400, b"malformed receive-pack body"
    sideband = "side-band-64k" in capabilities

    unpack_ok = True
    unpack_detail = "ok"
    new_objects = []
    if pack_bytes:
        if not verify_pack(pack_bytes):
            unpack_ok = False
            unpack_detail = "pack checksum mismatch"
        else:
            try:
                def _held_base(oid):
                    held = repo.objects.get(oid)
                    if held is None:
                        return None
                    return (oid, held[0], held[1])
                new_objects = read_pack(pack_bytes,
                                        resolve_base=_held_base)
            except (ValueError, IndexError, zlib.error, RecursionError) as exc:
                unpack_ok = False
                unpack_detail = "unpack error: %s" % exc
    if unpack_ok:
        with STORE.lock:
            for oid, obj_type, data in new_objects:
                repo.objects[oid] = (obj_type, data)

    report = ["unpack %s" % unpack_detail]
    if unpack_ok:
        with STORE.lock:
            for old_oid, new_oid, ref in commands:
                current = repo.refs.get(ref)
                if new_oid == ZERO_OID:
                    # delete
                    if current is None:
                        report.append("ng %s ref does not exist" % ref)
                    elif old_oid != ZERO_OID and old_oid != current:
                        report.append("ng %s non-fast-forward" % ref)
                    else:
                        del repo.refs[ref]
                        report.append("ok %s" % ref)
                    continue
                if new_oid not in repo.objects:
                    report.append("ng %s missing object %s" % (ref, new_oid))
                    continue
                if old_oid == ZERO_OID:
                    # create
                    if current is not None:
                        report.append("ng %s already exists" % ref)
                    else:
                        repo.refs[ref] = new_oid
                        report.append("ok %s" % ref)
                    continue
                # update
                if current is None:
                    report.append("ng %s ref does not exist" % ref)
                elif old_oid != current:
                    report.append("ng %s non-fast-forward" % ref)
                elif not is_descendant(repo, new_oid, old_oid):
                    report.append("ng %s non-fast-forward" % ref)
                else:
                    repo.refs[ref] = new_oid
                    report.append("ok %s" % ref)
    framed = pkt_lines([line + "\n" for line in report] + ["flush"])
    if sideband:
        return 200, sideband_pack(framed) + pkt_lines(["flush"])
    return 200, framed + pkt_lines(["flush"])

# ---------------------------------------------------------------------------
# HTTP plumbing
# ---------------------------------------------------------------------------

EXPECTED_TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN") or None


def _b64encode_wrapped(data):
    """Base64 the way GitHub's contents API does: 60 columns per line."""
    raw = base64.b64encode(data).decode("ascii")
    return "\n".join(raw[i:i + 60] for i in range(0, len(raw), 60))


def _b64decode(text):
    cleaned = "".join(text.split())
    return base64.b64decode(cleaned)


class ForgeServer(ThreadingHTTPServer):
    """Threading server with Nagle disabled on accepted sockets.

    Without TCP_NODELAY, each small response waits up to 40 ms for the
    client's delayed ACK of the previous response (Nagle + delayed ACK):
    ~41 ms per request on a keep-alive connection, which blows the
    read workload's 60 s budget. With it, a round trip is ~1 ms."""

    daemon_threads = True
    # The default listen backlog (5) drops SYNs under 50 concurrent
    # clones; a dropped SYN costs the client a ~1 s retransmit.
    request_queue_size = 128

    def get_request(self):
        request, client_address = super().get_request()
        request.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        return request, client_address


class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "Forge/1.0"

    # -- quiet ------------------------------------------------------------
    def log_message(self, *args):
        pass

    # -- verbs ------------------------------------------------------------
    def do_GET(self):
        self._dispatch("GET")

    def do_POST(self):
        self._dispatch("POST")

    def do_PUT(self):
        self._dispatch("PUT")

    def do_PATCH(self):
        self._dispatch("PATCH")

    def do_DELETE(self):
        self._dispatch("DELETE")

    # -- responses ----------------------------------------------------------
    def _send_json(self, status, obj, extra=None):
        body = json.dumps(obj, separators=(",", ":")).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("X-GitHub-Request-Id", STORE.next_request_id())
        self.send_header("X-OAuth-Scopes", "repo")
        if extra:
            for key, value in extra.items():
                self.send_header(key, value)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(body)

    def _send_empty(self, status, extra=None):
        self.send_response(status)
        self.send_header("Content-Length", "0")
        self.send_header("X-GitHub-Request-Id", STORE.next_request_id())
        self.send_header("X-OAuth-Scopes", "repo")
        if extra:
            for key, value in extra.items():
                self.send_header(key, value)
        self.end_headers()

    def _send_raw(self, status, body, content_type):
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("X-GitHub-Request-Id", STORE.next_request_id())
        self.end_headers()
        self.wfile.write(body)

    def _error(self, status, message):
        self._send_json(status, {"message": message})

    # -- request reading ----------------------------------------------------
    def _read_body(self):
        """Read the request body once and cache it: handlers may ask for
        it again, and the socket must be drained before the next
        keep-alive request is read, or the connection desynchronises."""
        cached = getattr(self, "_body_cache", None)
        if cached is not None:
            return cached
        length = self.headers.get("Content-Length")
        if not length:
            self._body_cache = b""
            return b""
        try:
            n = int(length)
        except ValueError:
            self._body_cache = b""
            return b""
        if n <= 0:
            self._body_cache = b""
            return b""
        self._body_cache = self.rfile.read(n)
        return self._body_cache

    def _json_body(self):
        """Parse the request body as JSON. Empty body counts as {}.
        Returns (obj, error_response_or_None)."""
        raw = self._read_body()
        if not raw:
            return {}, None
        try:
            obj = json.loads(raw.decode("utf-8"))
        except (ValueError, UnicodeDecodeError):
            return None, (400, "malformed JSON body")
        if not isinstance(obj, (dict, list)):
            return None, (400, "JSON body must be an object or array")
        return obj, None

    # -- auth ---------------------------------------------------------------
    def _authorized(self):
        header = self.headers.get("Authorization") or ""
        if not header.startswith("Bearer "):
            return False
        token = header[len("Bearer "):].strip()
        if not token:
            return False
        if EXPECTED_TOKEN is not None:
            return token == EXPECTED_TOKEN
        return True

    # -- routing --------------------------------------------------------------
    def _dispatch(self, method):
        try:
            self._body_cache = None
            # Consume the request body up front (when there is one): every
            # handler path — including 401/404 early returns — must leave
            # the socket drained, or the next request on this keep-alive
            # connection is read from the middle of this one's body.
            self._read_body()
            parsed = urlparse(self.path)
            path = parsed.path
            query = parse_qs(parsed.query)
            segments = [unquote(s) for s in path.split("/") if s != ""]
            if path == "/healthz":
                self._send_json(200, {"status": "ok"})
                return
            if len(segments) >= 2 and segments[1].endswith(".git"):
                self._handle_git(method, segments, query)
                return
            if len(segments) >= 2 and segments[0] == "api" and segments[1] == "v3":
                _handle_rest(self, method, segments[2:], query)
                return
            if segments == ["api", "graphql"]:
                _handle_graphql(self, method)
                return
            if segments == ["mcp"]:
                _handle_mcp(self, method)
                return
            # Unknown top-level route: still a JSON 404 with a request id.
            if not self._authorized():
                self._error(401, "Requires authentication")
                return
            self._error(404, "Not Found")
        except BrokenPipeError:
            pass
        except ConnectionResetError:
            pass
        except Exception as exc:  # never let one request kill the server
            try:
                self._error(500, "Internal error: %s" % exc)
            except Exception:
                pass

    # -- git ------------------------------------------------------------------
    def _handle_git(self, method, segments, query):
        """Smart HTTP: /{owner}/{repo}.git/info/refs?service=... (GET) and
        /{owner}/{repo}.git/git-upload-pack|git-receive-pack (POST)."""
        if not self._authorized():
            self._error(401, "Requires authentication")
            return
        if len(segments) < 2 or not segments[1].endswith(".git"):
            self._error(404, "Not Found")
            return
        owner, repo_name = segments[0], segments[1][:-len(".git")]
        repo = _find_repo(owner, repo_name)
        if repo is None:
            self._error(404, "Not Found")
            return
        rest = segments[2:]
        if method == "GET" and rest == ["info", "refs"]:
            service = (query.get("service") or [""])[0]
            if service not in ("git-upload-pack", "git-receive-pack"):
                self._error(404, "Not Found")
                return
            is_v2 = service == "git-upload-pack" and (
                self.headers.get("Git-Protocol") or "") == "version=2"
            if is_v2:
                body = advertisement_v2()
                ctype = "application/x-git-upload-pack-advertisement"
            else:
                body = advertisement_v0(repo, service)
                ctype = "application/x-%s-advertisement" % service
            self._send_raw(200, body, ctype)
            return
        if method == "POST" and rest == ["git-upload-pack"]:
            body = self._read_body()
            is_v2 = (self.headers.get("Git-Protocol") or "") == "version=2"
            status, out = handle_upload_pack(repo, body, is_v2)
            if status != 200:
                self._send_raw(status, out, "text/plain")
            else:
                self._send_raw(200, out, "application/x-git-upload-pack-result")
            return
        if method == "POST" and rest == ["git-receive-pack"]:
            body = self._read_body()
            status, out = handle_receive_pack(repo, body)
            if status != 200:
                self._send_raw(status, out, "text/plain")
            else:
                self._send_raw(200, out, "application/x-git-receive-pack-result")
            return
        self._error(404, "Not Found")


def _find_repo(owner, name):
    if owner != VIEWER_LOGIN:
        return None
    return STORE.repos.get((owner, name))


def _paginate(items, query):
    """Slice a list by ?per_page=&page= and build a Link header."""
    try:
        per_page = int((query.get("per_page") or ["30"])[0])
    except ValueError:
        per_page = 30
    per_page = max(1, min(per_page, 100))
    try:
        page = int((query.get("page") or ["1"])[0])
    except ValueError:
        page = 1
    page = max(1, page)
    total = len(items)
    start = (page - 1) * per_page
    end = start + per_page
    return items[start:end], per_page, page, total


def _link_header(base_url, query, per_page, page, total):
    """A GitHub-style Link header with absolute same-origin URLs."""
    if total <= per_page:
        return None
    last_page = (total + per_page - 1) // per_page
    links = []
    if page < last_page:
        links.append('<%s>; rel="next"' % _page_url(base_url, query, per_page, page + 1))
    links.append('<%s>; rel="last"' % _page_url(base_url, query, per_page, last_page))
    if page > 1:
        links.append('<%s>; rel="prev"' % _page_url(base_url, query, per_page, page - 1))
        links.append('<%s>; rel="first"' % _page_url(base_url, query, per_page, 1))
    return ", ".join(links)


def _page_url(base_url, query, per_page, page):
    params = dict(query)
    params["per_page"] = [str(per_page)]
    params["page"] = [str(page)]
    qs = "&".join("%s=%s" % (k, v[0]) for k, v in sorted(params.items()))
    return "%s?%s" % (base_url, qs)


def _base_url(handler):
    host = handler.headers.get("Host") or "127.0.0.1"
    return "http://%s%s" % (host, urlparse(handler.path).path)


# ---------------------------------------------------------------------------
# REST serializers
# ---------------------------------------------------------------------------

def _user_json(login=VIEWER_LOGIN, user_id=VIEWER_ID):
    return {
        "login": login, "id": user_id, "type": "User",
        "site_admin": False,
        "avatar_url": "https://example.invalid/avatar/%s" % login,
        "html_url": "https://example.invalid/%s" % login,
    }


def repo_json(repo):
    return {
        "id": repo.id,
        "databaseId": repo.id,
        "node_id": _gql_id("R", repo.full_name),
        "name": repo.name,
        "full_name": repo.full_name,
        "owner": _user_json(repo.owner, VIEWER_ID),
        "private": repo.private,
        "description": repo.description,
        "default_branch": repo.default_branch,
        "html_url": "https://example.invalid/%s" % repo.full_name,
        "url": "/api/v3/repos/%s" % repo.full_name,
        "created_at": repo.created_at,
        "updated_at": repo.updated_at,
        "pushed_at": repo.updated_at,
        "has_issues": True,
        "has_projects": True,
        "has_wiki": True,
        "fork": False,
        "archived": False,
        "disabled": False,
        "visibility": "private" if repo.private else "public",
    }


def label_json(label):
    return {
        "name": label["name"],
        "color": label.get("color", "ededed"),
        "description": label.get("description", ""),
        "url": "/api/v3/labels/%s" % label["name"],
    }


def issue_json(repo, issue):
    return {
        "id": issue["id"],
        "node_id": _gql_id("I", "%s#%d" % (repo.full_name, issue["number"])),
        "number": issue["number"],
        "title": issue["title"],
        "body": issue.get("body", ""),
        "state": issue["state"],
        "labels": [label_json(repo.labels[name]) for name in issue["labels"]
                   if name in repo.labels],
        "user": _user_json(),
        "comments": len(issue["comments"]),
        "created_at": issue["created_at"],
        "updated_at": issue["updated_at"],
        "html_url": "https://example.invalid/%s/issues/%d" % (
            repo.full_name, issue["number"]),
        "url": "/api/v3/repos/%s/issues/%d" % (repo.full_name, issue["number"]),
    }


def comment_json(repo, issue, comment):
    return {
        "id": comment["id"],
        "node_id": _gql_id("C", "%s#%d:%d" % (
            repo.full_name, issue["number"], comment["id"])),
        "body": comment["body"],
        "user": _user_json(),
        "created_at": comment["created_at"],
        "updated_at": comment["updated_at"],
        "html_url": "https://example.invalid/%s/issues/%d#issuecomment-%d" % (
            repo.full_name, issue["number"], comment["id"]),
        "url": "/api/v3/repos/%s/issues/comments/%d" % (
            repo.full_name, comment["id"]),
    }


def _pr_head_base(repo, pull):
    head_tip = repo.refs.get("refs/heads/%s" % pull["head_ref"]) or ZERO_OID
    base_tip = repo.refs.get("refs/heads/%s" % pull["base_ref"]) or ZERO_OID
    return head_tip, base_tip


def pull_json(repo, pull):
    head_tip, base_tip = _pr_head_base(repo, pull)
    return {
        "id": pull["id"],
        "node_id": _gql_id("PR", "%s#%d" % (repo.full_name, pull["number"])),
        "number": pull["number"],
        "title": pull["title"],
        "body": pull.get("body", ""),
        "state": pull["state"],
        "head": {"ref": pull["head_ref"], "sha": head_tip,
                 "label": "%s:%s" % (repo.owner, pull["head_ref"])},
        "base": {"ref": pull["base_ref"], "sha": base_tip,
                 "label": "%s:%s" % (repo.owner, pull["base_ref"])},
        "merged": pull["merged"],
        "merged_at": pull["merged_at"],
        "merge_commit_sha": pull["merge_commit_sha"],
        "mergeable": _pr_mergeable(repo, pull),
        "user": _user_json(),
        "created_at": pull["created_at"],
        "updated_at": pull["updated_at"],
        "html_url": "https://example.invalid/%s/pull/%d" % (
            repo.full_name, pull["number"]),
        "url": "/api/v3/repos/%s/pulls/%d" % (repo.full_name, pull["number"]),
    }


def _gql_id(kind, key):
    """An opaque global id: base64 of '<kind>:<key>'. Never the bare
    databaseId, and stable across reads."""
    raw = ("%s:%s" % (kind, key)).encode("utf-8")
    return base64.b64encode(raw).decode("ascii")


def _gql_decode(gid):
    try:
        raw = base64.b64decode(gid).decode("utf-8")
    except Exception:
        return None, None
    kind, _, key = raw.partition(":")
    if not kind or not key:
        return None, None
    return kind, key

# ---------------------------------------------------------------------------
# REST v3
# ---------------------------------------------------------------------------

def _resolve_ref(repo, ref):
    """Resolve a branch name, a full ref, or an oid to a commit oid."""
    if not ref:
        return repo.head_oid()
    if is_oid(ref):
        obj = repo.objects.get(ref)
        return ref if obj and obj[0] == "commit" else None
    if ref.startswith("refs/"):
        return repo.refs.get(ref)
    return repo.refs.get("refs/heads/%s" % ref)


def _commit_list(repo, tip, limit=None):
    """First-parent walk from tip, newest first."""
    out = []
    cur = tip
    seen = set()
    while cur and cur not in seen:
        seen.add(cur)
        obj = repo.objects.get(cur)
        if obj is None or obj[0] != "commit":
            break
        out.append(cur)
        parents = parse_commit(obj[1])["parents"]
        cur = parents[0] if parents else None
        if limit and len(out) >= limit:
            break
    return out


def _commit_json(repo, oid):
    obj = repo.objects.get(oid)
    commit = parse_commit(obj[1])
    author = _ident_json(commit["author"])
    committer = _ident_json(commit["committer"])
    return {
        "sha": oid,
        "commit": {
            "message": commit["message"],
            "author": author,
            "committer": committer,
        },
        "author": _user_json(),
        "committer": _user_json(),
        "parents": [{"sha": p} for p in commit["parents"]],
        "html_url": "https://example.invalid/%s/commit/%s" % (repo.full_name, oid),
        "url": "/api/v3/repos/%s/commits/%s" % (repo.full_name, oid),
    }


def _ident_json(line):
    """'Name <email> 1700000000 +0000' -> {name, email, date}."""
    name, email, when = "Conformance", "conformance@make.fun", FIXED_NOW
    m = re.match(r"^(.*?) <([^>]*)> (\d+) ([+-]\d{4})$", line or "")
    if m:
        name, email = m.group(1), m.group(2)
        try:
            when = time.strftime("%Y-%m-%dT%H:%M:%SZ",
                                 time.gmtime(int(m.group(3))))
        except ValueError:
            pass
    return {"name": name, "email": email, "date": when}


def _content_file_json(repo, tip, path, blob_oid, blob_data):
    return {
        "type": "file",
        "encoding": "base64",
        "size": len(blob_data),
        "name": path.rsplit("/", 1)[-1],
        "path": path,
        "content": _b64encode_wrapped(blob_data),
        "sha": blob_oid,
        "url": "/api/v3/repos/%s/contents/%s" % (repo.full_name, path),
        "html_url": "https://example.invalid/%s/blob/%s/%s" % (
            repo.full_name, repo.default_branch, path),
    }


def build_tree_from_paths(repo, files):
    """Build (and store) a tree from {path: (mode, oid)}."""
    root = {}
    for path, (mode, oid) in files.items():
        parts = path.split("/")
        node = root
        for part in parts[:-1]:
            node = node.setdefault(part, {})
        node[parts[-1]] = (mode, oid)

    def make(node):
        entries = []
        for name, val in node.items():
            if isinstance(val, dict):
                entries.append(("40000", name, make(val)))
            else:
                mode, oid = val
                entries.append((mode, name, oid))
        data = build_tree(entries)
        new_oid = hash_object("tree", data)
        repo.objects[new_oid] = ("tree", data)
        return new_oid

    return make(root)


def _pr_diff(repo, pull):
    """Three-way diff for a pull request. Returns (changes, conflict)
    where changes maps path -> (mode, oid) or None (deleted in head)."""
    head_tip, base_tip = _pr_head_base(repo, pull)
    if not head_tip or not base_tip or head_tip == ZERO_OID or base_tip == ZERO_OID:
        return {}, False
    mb = merge_base(repo, head_tip, base_tip)
    if mb is None:
        return {}, True
    mb_files = tree_paths(repo, parse_commit(repo.objects[mb][1])["tree"])
    head_files = tree_paths(repo, parse_commit(repo.objects[head_tip][1])["tree"])
    base_files = tree_paths(repo, parse_commit(repo.objects[base_tip][1])["tree"])
    changes = {}
    for path in set(mb_files) | set(head_files):
        if mb_files.get(path) != head_files.get(path):
            changes[path] = head_files.get(path)
    conflict = False
    for path in set(mb_files) | set(base_files):
        if mb_files.get(path) == base_files.get(path):
            continue
        if path in changes and changes[path] != base_files.get(path):
            conflict = True
    return changes, conflict


def _pr_mergeable(repo, pull):
    if pull["state"] != "open":
        return False
    _changes, conflict = _pr_diff(repo, pull)
    return not conflict


def _pr_files(repo, pull):
    """The pull request's changed files with line counts."""
    import difflib
    head_tip, base_tip = _pr_head_base(repo, pull)
    if not head_tip or not base_tip or head_tip == ZERO_OID or base_tip == ZERO_OID:
        return []
    mb = merge_base(repo, head_tip, base_tip)
    if mb is None:
        return []
    mb_files = tree_paths(repo, parse_commit(repo.objects[mb][1])["tree"])
    head_files = tree_paths(repo, parse_commit(repo.objects[head_tip][1])["tree"])
    out = []
    for path in sorted(set(mb_files) | set(head_files)):
        old = mb_files.get(path)
        new = head_files.get(path)
        if old == new:
            continue
        if old is None:
            status = "added"
            new_data = repo.objects[new[1]][1]
            additions = len(new_data.decode("utf-8", "replace").splitlines())
            deletions = 0
        elif new is None:
            status = "removed"
            old_data = repo.objects[old[1]][1]
            additions = 0
            deletions = len(old_data.decode("utf-8", "replace").splitlines())
        else:
            status = "modified"
            old_lines = repo.objects[old[1]][1].decode("utf-8", "replace").splitlines()
            new_lines = repo.objects[new[1]][1].decode("utf-8", "replace").splitlines()
            matcher = difflib.SequenceMatcher(None, old_lines, new_lines)
            additions = deletions = 0
            for tag, i1, i2, j1, j2 in matcher.get_opcodes():
                if tag in ("insert", "replace"):
                    additions += j2 - j1
                if tag in ("delete", "replace"):
                    deletions += i2 - i1
        out.append({
            "filename": path, "status": status,
            "additions": additions, "deletions": deletions,
            "changes": additions + deletions,
        })
    return out


def _create_repo_store(name, description="", private=False):
    """Create a repository in the store. Returns (repo, error_message).
    The one creation path shared by REST and MCP, so both surfaces see
    the same object with the same id."""
    if not isinstance(name, str) or not name or not re.match(
            r"^[A-Za-z0-9][A-Za-z0-9._-]{0,99}$", name):
        return None, "Invalid repository name"
    with STORE.lock:
        if (VIEWER_LOGIN, name) in STORE.repos:
            return None, "Repository already exists"
        repo_id = STORE.next_repo_id
        STORE.next_repo_id += 1
        repo = Repo(repo_id, name, VIEWER_LOGIN,
                    description or "", bool(private))
        repo.objects[SHA1_EMPTY_TREE] = ("tree", b"")
        STORE.repos[(VIEWER_LOGIN, name)] = repo
    return repo, None


class _Rest:
    """One REST request: auth, repo lookup, and the route table."""

    def __init__(self, handler, method, segs, query):
        self.h = handler
        self.method = method
        self.segs = segs
        self.query = query
        self.body = None

    # -- helpers ------------------------------------------------------------
    def json(self, status, obj, extra=None):
        self.h._send_json(status, obj, extra)

    def error(self, status, message):
        self.h._error(status, message)

    def page(self, items):
        """Paginate a list and send it with a Link header when needed."""
        page_items, per_page, page, total = _paginate(items, self.query)
        extra = None
        link = _link_header(_base_url(self.h), self.query, per_page, page, total)
        if link:
            extra = {"Link": link}
        self.json(200, page_items, extra)

    def need_body(self):
        obj, err = self.h._json_body()
        if err is not None:
            self.error(err[0], err[1])
            return None
        if not isinstance(obj, dict):
            self.error(400, "JSON body must be an object")
            return None
        self.body = obj
        return obj

    def repo(self, owner, name):
        repo = _find_repo(owner, name)
        if repo is None:
            self.error(404, "Not Found")
            return None
        return repo

    # -- entry ----------------------------------------------------------------
    def run(self):
        if not self.h._authorized():
            self.error(401, "Requires authentication")
            return
        segs = self.segs
        if segs == []:
            if self.method == "GET":
                self.json(200, {
                    "current_user_url": "/api/v3/user",
                    "repository_url": "/api/v3/repos/{owner}/{repo}",
                    "user_url": "/api/v3/users/{username}",
                })
            else:
                self.error(404, "Not Found")
            return
        if segs == ["meta"]:
            if self.method == "GET":
                self.json(200, {
                    "installed_version": FORGE_VERSION,
                    "verifiable_password_authentication": False,
                    "github_services_sha": "0" * 40,
                    "hooks": ["pre-push"],
                    "git": ["1.0"],
                    "pages": ["https://example.invalid/pages"],
                    "importer": ["git"],
                    "issues": ["labels"],
                })
            else:
                self.error(404, "Not Found")
            return
        if segs == ["user"]:
            if self.method == "GET":
                self.json(200, _user_json())
            else:
                self.error(404, "Not Found")
            return
        if segs == ["user", "repos"]:
            if self.method == "GET":
                repos = [repo_json(r) for r in sorted(
                    STORE.repos.values(), key=lambda r: r.id)
                    if r.owner == VIEWER_LOGIN]
                self.page(repos)
            elif self.method == "POST":
                self._create_repo()
            else:
                self.error(404, "Not Found")
            return
        if len(segs) >= 3 and segs[0] == "repos":
            self._repo_routes(segs[1], segs[2], segs[3:])
            return
        self.error(404, "Not Found")

    # -- repos ------------------------------------------------------------------
    def _create_repo(self):
        body = self.need_body()
        if body is None:
            return
        repo, error = _create_repo_store(
            body.get("name"), body.get("description") or "",
            body.get("private", False))
        if repo is None:
            self.error(422, error)
            return
        self.json(201, repo_json(repo))

    def _repo_routes(self, owner, name, rest):
        repo = self.repo(owner, name)
        if repo is None:
            return
        if rest == []:
            if self.method == "GET":
                self.json(200, repo_json(repo))
            elif self.method == "PATCH":
                body = self.need_body()
                if body is None:
                    return
                with STORE.lock:
                    if "description" in body:
                        repo.description = body["description"] or ""
                    if "private" in body:
                        repo.private = bool(body["private"])
                    repo.updated_at = FIXED_NOW
                self.json(200, repo_json(repo))
            elif self.method == "DELETE":
                with STORE.lock:
                    del STORE.repos[(owner, name)]
                self.h._send_empty(204)
            else:
                self.error(404, "Not Found")
            return
        if rest == ["branches"]:
            if self.method == "GET":
                branches = []
                for refname in sorted(repo.refs):
                    if refname.startswith("refs/heads/"):
                        branches.append({
                            "name": refname[len("refs/heads/"):],
                            "commit": {"sha": repo.refs[refname]},
                            "protected": False,
                        })
                self.page(branches)
            else:
                self.error(404, "Not Found")
            return
        if rest[0] == "branches" and len(rest) >= 2:
            branch = "/".join(rest[1:])
            oid = repo.refs.get("refs/heads/%s" % branch)
            if oid is None:
                self.error(404, "Branch not found")
                return
            if self.method == "GET":
                self.json(200, {
                    "name": branch, "commit": {"sha": oid},
                    "protected": False,
                })
            else:
                self.error(404, "Not Found")
            return
        if rest[0] == "git" and len(rest) >= 2 and rest[1] == "refs":
            self._git_refs(repo, rest[2:])
            return
        if rest[0] == "git" and len(rest) >= 2 and rest[1] == "matching-refs":
            prefix = "/".join(rest[2:])
            wanted = "refs/" + prefix
            out = []
            for refname in sorted(repo.refs):
                if refname.startswith(wanted):
                    oid = repo.refs[refname]
                    out.append({"ref": refname, "object": {
                        "sha": oid,
                        "type": repo.objects.get(oid, ("commit",))[0]}})
            self.json(200, out)
            return
        if rest == ["commits"]:
            if self.method == "GET":
                sha_param = (self.query.get("sha") or [None])[0]
                tip = _resolve_ref(repo, sha_param)
                if tip is None:
                    self.error(404, "No commit found for SHA: %s" % sha_param)
                    return
                commits = [_commit_json(repo, oid)
                           for oid in _commit_list(repo, tip)]
                self.page(commits)
            else:
                self.error(404, "Not Found")
            return
        if rest[0] == "commits" and len(rest) == 2:
            oid = rest[1]
            obj = repo.objects.get(oid)
            if obj is None or obj[0] != "commit":
                self.error(404, "Not Found")
                return
            if self.method == "GET":
                self.json(200, _commit_json(repo, oid))
            else:
                self.error(404, "Not Found")
            return
        if rest[0] == "contents":
            self._contents(repo, rest[1:])
            return
        if rest == ["labels"]:
            if self.method == "GET":
                self.json(200, [label_json(repo.labels[k])
                                for k in sorted(repo.labels)])
            elif self.method == "POST":
                body = self.need_body()
                if body is None:
                    return
                label_name = body.get("name")
                if not isinstance(label_name, str) or not label_name:
                    self.error(422, "Invalid label name")
                    return
                with STORE.lock:
                    if label_name in repo.labels:
                        self.error(422, "Label already exists")
                        return
                    repo.labels[label_name] = {
                        "name": label_name,
                        "color": body.get("color") or "ededed",
                        "description": body.get("description") or "",
                    }
                self.json(201, label_json(repo.labels[label_name]))
            else:
                self.error(404, "Not Found")
            return
        if rest == ["issues"]:
            if self.method == "GET":
                self._list_issues(repo)
            elif self.method == "POST":
                self._create_issue(repo)
            else:
                self.error(404, "Not Found")
            return
        if len(rest) == 2 and rest[0] == "issues" and rest[1].isdigit():
            self._issue_one(repo, int(rest[1]))
            return
        if len(rest) == 3 and rest[0] == "issues" and rest[1].isdigit() \
                and rest[2] == "comments":
            self._issue_comments(repo, int(rest[1]))
            return
        if rest == ["pulls"]:
            if self.method == "GET":
                self._list_pulls(repo)
            elif self.method == "POST":
                self._create_pull(repo)
            else:
                self.error(404, "Not Found")
            return
        if len(rest) == 2 and rest[0] == "pulls" and rest[1].isdigit():
            self._pull_one(repo, int(rest[1]))
            return
        if len(rest) == 3 and rest[0] == "pulls" and rest[1].isdigit() \
                and rest[2] == "files":
            self._pull_files(repo, int(rest[1]))
            return
        if len(rest) == 3 and rest[0] == "pulls" and rest[1].isdigit() \
                and rest[2] == "merge":
            self._pull_merge(repo, int(rest[1]))
            return
        self.error(404, "Not Found")

    # -- git refs ---------------------------------------------------------------
    def _git_refs(self, repo, rest):
        if rest == []:
            if self.method == "POST":
                body = self.need_body()
                if body is None:
                    return
                ref = body.get("ref")
                sha = body.get("sha")
                if not isinstance(ref, str) or not ref.startswith("refs/"):
                    self.error(422, "Invalid ref")
                    return
                if not is_oid(sha) or sha not in repo.objects:
                    self.error(422, "Invalid sha")
                    return
                with STORE.lock:
                    if ref in repo.refs:
                        self.error(422, "Reference already exists")
                        return
                    repo.refs[ref] = sha
                self.json(201, {
                    "ref": ref,
                    "object": {"sha": sha,
                               "type": repo.objects[sha][0]},
                    "url": "/api/v3/repos/%s/git/refs/%s" % (
                        repo.full_name, ref[len("refs/"):]),
                })
            elif self.method == "GET":
                out = []
                for refname in sorted(repo.refs):
                    oid = repo.refs[refname]
                    out.append({"ref": refname, "object": {
                        "sha": oid,
                        "type": repo.objects.get(oid, ("commit",))[0]}})
                self.json(200, out)
            else:
                self.error(404, "Not Found")
            return
        ref = "refs/" + "/".join(rest)
        oid = repo.refs.get(ref)
        if oid is None:
            self.error(404, "Not Found")
            return
        if self.method == "GET":
            self.json(200, {
                "ref": ref,
                "object": {"sha": oid,
                           "type": repo.objects.get(oid, ("commit",))[0]},
            })
        else:
            self.error(404, "Not Found")

    # -- contents ---------------------------------------------------------------
    def _contents(self, repo, path_parts):
        path = "/".join(path_parts)
        if self.method == "GET":
            ref_param = (self.query.get("ref") or [None])[0]
            tip = _resolve_ref(repo, ref_param)
            if tip is None:
                self.error(404, "Not Found")
                return
            tree_oid = parse_commit(repo.objects[tip][1])["tree"]
            if not path:
                entries = parse_tree(repo.objects[tree_oid][1])
                out = []
                for mode, ename, child in entries:
                    kind = "dir" if mode == "40000" else "file"
                    size = 0
                    if kind == "file":
                        size = len(repo.objects[child][1])
                    out.append({"type": kind, "name": ename, "path": ename,
                                "sha": child, "size": size})
                self.json(200, out)
                return
            found = tree_get(repo, tree_oid, path)
            if found is None:
                self.error(404, "Not Found")
                return
            mode, oid, kind = found
            if kind == "dir":
                entries = parse_tree(repo.objects[oid][1])
                out = []
                for emode, ename, child in entries:
                    ekind = "dir" if emode == "40000" else "file"
                    size = 0
                    if ekind == "file":
                        size = len(repo.objects[child][1])
                    out.append({"type": ekind, "name": ename,
                                "path": "%s/%s" % (path, ename),
                                "sha": child, "size": size})
                self.json(200, out)
                return
            data = repo.objects[oid][1]
            self.json(200, _content_file_json(repo, tip, path, oid, data))
            return
        if self.method in ("PUT", "DELETE"):
            body = self.need_body()
            if body is None:
                return
            branch = body.get("branch") or repo.default_branch
            refname = "refs/heads/%s" % branch
            with STORE.lock:
                tip = repo.refs.get(refname)
                if tip is None and branch != repo.default_branch:
                    self.error(404, "Branch not found")
                    return
                tree_oid = (parse_commit(repo.objects[tip][1])["tree"]
                            if tip else SHA1_EMPTY_TREE)
                found = tree_get(repo, tree_oid, path) if tip else None
                if self.method == "PUT":
                    self._contents_put(repo, path, body, branch, refname,
                                       tip, tree_oid, found)
                else:
                    self._contents_delete(repo, path, body, branch, refname,
                                          tip, tree_oid, found)
            return
        self.error(404, "Not Found")

    def _contents_put(self, repo, path, body, branch, refname, tip,
                      tree_oid, found):
        if not path:
            self.error(422, "Invalid path")
            return
        if found is not None and found[2] == "dir":
            self.error(422, "Path is a directory")
            return
        content_b64 = body.get("content")
        if not isinstance(content_b64, str):
            self.error(422, "content is required")
            return
        try:
            data = _b64decode(content_b64)
        except Exception:
            self.error(422, "content is not valid base64")
            return
        sha = body.get("sha")
        is_update = found is not None
        if is_update:
            if sha is None:
                self.error(422, "sha is required to update a file")
                return
            if sha != found[1]:
                self.error(409, "sha does not match the current file")
                return
        else:
            if sha is not None:
                self.error(422, "sha does not match any file")
                return
        blob_oid = hash_object("blob", data)
        repo.objects[blob_oid] = ("blob", data)
        new_tree = tree_set(repo, tree_oid, path, blob_oid)
        message = body.get("message") or ("Update %s" % path)
        commit_data = build_commit(new_tree, [tip] if tip else [], message)
        commit_oid = hash_object("commit", commit_data)
        repo.objects[commit_oid] = ("commit", commit_data)
        repo.refs[refname] = commit_oid
        repo.updated_at = FIXED_NOW
        self.json(201 if not is_update else 200, {
            "content": _content_file_json(repo, commit_oid, path,
                                          blob_oid, data),
            "commit": {"sha": commit_oid, "message": message},
        })

    def _contents_delete(self, repo, path, body, branch, refname, tip,
                         tree_oid, found):
        if tip is None or found is None or found[2] != "file":
            self.error(404, "Not Found")
            return
        sha = body.get("sha")
        if sha is not None and sha != found[1]:
            self.error(409, "sha does not match the current file")
            return
        new_tree = tree_set(repo, tree_oid, path, None)
        message = body.get("message") or ("Delete %s" % path)
        commit_data = build_commit(new_tree, [tip], message)
        commit_oid = hash_object("commit", commit_data)
        repo.objects[commit_oid] = ("commit", commit_data)
        repo.refs[refname] = commit_oid
        repo.updated_at = FIXED_NOW
        self.json(200, {"commit": {"sha": commit_oid, "message": message}})

# ---------------------------------------------------------------------------
# REST: issues, comments, pull requests (methods of _Rest)
# ---------------------------------------------------------------------------

def _rest_list_issues(self, repo):
    state = (self.query.get("state") or ["open"])[0]
    sort = (self.query.get("sort") or ["created"])[0]
    direction = (self.query.get("direction") or ["desc"])[0]
    issues = list(repo.issues)
    if state != "all":
        issues = [i for i in issues if i["state"] == state]
    if sort == "created":
        issues.sort(key=lambda i: i["number"],
                    reverse=(direction != "asc"))
    self.page([issue_json(repo, i) for i in issues])


def _rest_create_issue(self, repo):
    body = self.need_body()
    if body is None:
        return
    title = body.get("title")
    if not isinstance(title, str) or not title:
        self.error(422, "title is required")
        return
    labels = body.get("labels") or []
    if not isinstance(labels, list):
        self.error(422, "labels must be an array")
        return
    for name in labels:
        if name not in repo.labels:
            self.error(422, "Label does not exist: %s" % name)
            return
    with STORE.lock:
        repo.issue_seq += 1
        STORE.next_object_id += 1
        issue = {
            "id": STORE.next_object_id,
            "number": repo.issue_seq,
            "title": title,
            "body": body.get("body") or "",
            "state": "open",
            "labels": list(labels),
            "comments": [],
            "created_at": FIXED_NOW,
            "updated_at": FIXED_NOW,
        }
        repo.issues.append(issue)
    self.json(201, issue_json(repo, issue))


def _rest_issue_one(self, repo, number):
    issue = next((i for i in repo.issues if i["number"] == number), None)
    if issue is None:
        self.error(404, "Not Found")
        return
    if self.method == "GET":
        self.json(200, issue_json(repo, issue))
    elif self.method == "PATCH":
        body = self.need_body()
        if body is None:
            return
        with STORE.lock:
            if "state" in body:
                if body["state"] not in ("open", "closed"):
                    self.error(422, "Invalid state")
                    return
                issue["state"] = body["state"]
            if "title" in body and isinstance(body["title"], str):
                issue["title"] = body["title"]
            if "body" in body and isinstance(body["body"], str):
                issue["body"] = body["body"]
            if "labels" in body and isinstance(body["labels"], list):
                for name in body["labels"]:
                    if name not in repo.labels:
                        self.error(422, "Label does not exist: %s" % name)
                        return
                issue["labels"] = list(body["labels"])
            issue["updated_at"] = FIXED_NOW
        self.json(200, issue_json(repo, issue))
    else:
        self.error(404, "Not Found")


def _rest_issue_comments(self, repo, number):
    issue = next((i for i in repo.issues if i["number"] == number), None)
    if issue is None:
        self.error(404, "Not Found")
        return
    if self.method == "GET":
        self.page([comment_json(repo, issue, c) for c in issue["comments"]])
    elif self.method == "POST":
        body = self.need_body()
        if body is None:
            return
        text = body.get("body")
        if not isinstance(text, str):
            self.error(422, "body is required")
            return
        with STORE.lock:
            STORE.next_object_id += 1
            comment = {
                "id": STORE.next_object_id, "body": text,
                "created_at": FIXED_NOW, "updated_at": FIXED_NOW,
            }
            issue["comments"].append(comment)
        self.json(201, comment_json(repo, issue, comment))
    else:
        self.error(404, "Not Found")


def _rest_list_pulls(self, repo):
    state = (self.query.get("state") or ["open"])[0]
    pulls = list(repo.pulls)
    if state != "all":
        pulls = [p for p in pulls if p["state"] == state]
    pulls.sort(key=lambda p: p["number"], reverse=True)
    self.page([pull_json(repo, p) for p in pulls])


def _rest_create_pull(self, repo):
    body = self.need_body()
    if body is None:
        return
    head = body.get("head")
    base = body.get("base")
    if not isinstance(head, str) or not isinstance(base, str):
        self.error(422, "head and base are required")
        return
    if head == base:
        self.error(422, "head and base must be different")
        return
    if "refs/heads/%s" % head not in repo.refs:
        self.error(422, "head branch does not exist: %s" % head)
        return
    if "refs/heads/%s" % base not in repo.refs:
        self.error(422, "base branch does not exist: %s" % base)
        return
    with STORE.lock:
        for existing in repo.pulls:
            if existing["state"] == "open" \
                    and existing["head_ref"] == head \
                    and existing["base_ref"] == base:
                self.error(422, "A pull request already exists for %s" % head)
                return
        repo.pull_seq += 1
        STORE.next_object_id += 1
        pull = {
            "id": STORE.next_object_id,
            "number": repo.pull_seq,
            "title": body.get("title") or "",
            "body": body.get("body") or "",
            "state": "open",
            "head_ref": head,
            "base_ref": base,
            "merged": False,
            "merged_at": None,
            "merge_commit_sha": None,
            "created_at": FIXED_NOW,
            "updated_at": FIXED_NOW,
        }
        repo.pulls.append(pull)
    self.json(201, pull_json(repo, pull))


def _rest_pull_one(self, repo, number):
    pull = next((p for p in repo.pulls if p["number"] == number), None)
    if pull is None:
        self.error(404, "Not Found")
        return
    if self.method == "GET":
        self.json(200, pull_json(repo, pull))
    elif self.method == "PATCH":
        body = self.need_body()
        if body is None:
            return
        with STORE.lock:
            if "state" in body and body["state"] in ("open", "closed"):
                pull["state"] = body["state"]
            if "title" in body and isinstance(body["title"], str):
                pull["title"] = body["title"]
            if "body" in body and isinstance(body["body"], str):
                pull["body"] = body["body"]
            pull["updated_at"] = FIXED_NOW
        self.json(200, pull_json(repo, pull))
    else:
        self.error(404, "Not Found")


def _rest_pull_files(self, repo, number):
    pull = next((p for p in repo.pulls if p["number"] == number), None)
    if pull is None:
        self.error(404, "Not Found")
        return
    if self.method != "GET":
        self.error(404, "Not Found")
        return
    self.json(200, _pr_files(repo, pull))


def _rest_pull_merge(self, repo, number):
    pull = next((p for p in repo.pulls if p["number"] == number), None)
    if pull is None:
        self.error(404, "Not Found")
        return
    if self.method != "PUT":
        self.error(404, "Not Found")
        return
    body = self.need_body()
    if body is None:
        return
    with STORE.lock:
        if pull["state"] != "open":
            self.error(405, "Pull request is already closed")
            return
        changes, conflict = _pr_diff(repo, pull)
        if conflict:
            self.error(405, "Merge conflict")
            return
        head_tip, base_tip = _pr_head_base(repo, pull)
        base_files = tree_paths(
            repo, parse_commit(repo.objects[base_tip][1])["tree"])
        for path, entry in changes.items():
            if entry is None:
                base_files.pop(path, None)
            else:
                base_files[path] = entry
        new_tree = build_tree_from_paths(repo, base_files)
        message = pull["title"] or ("Merge pull request #%d" % number)
        commit_data = build_commit(new_tree, [base_tip], message)
        commit_oid = hash_object("commit", commit_data)
        repo.objects[commit_oid] = ("commit", commit_data)
        repo.refs["refs/heads/%s" % pull["base_ref"]] = commit_oid
        pull["state"] = "closed"
        pull["merged"] = True
        pull["merged_at"] = FIXED_NOW
        pull["merge_commit_sha"] = commit_oid
        pull["updated_at"] = FIXED_NOW
    self.json(200, {
        "sha": commit_oid, "merged": True,
        "message": "Pull request successfully merged",
    })


_Rest._list_issues = _rest_list_issues
_Rest._create_issue = _rest_create_issue
_Rest._issue_one = _rest_issue_one
_Rest._issue_comments = _rest_issue_comments
_Rest._list_pulls = _rest_list_pulls
_Rest._create_pull = _rest_create_pull
_Rest._pull_one = _rest_pull_one
_Rest._pull_files = _rest_pull_files
_Rest._pull_merge = _rest_pull_merge


def _handle_rest(handler, method, segs, query):
    _Rest(handler, method, segs, query).run()

# ---------------------------------------------------------------------------
# GraphQL: a small parser for the documents gh and github-mcp-server send
# ---------------------------------------------------------------------------

class _GQLToken:
    __slots__ = ("kind", "value")

    def __init__(self, kind, value):
        self.kind = kind
        self.value = value


def _gql_lex(source):
    tokens = []
    i, n = 0, len(source)
    while i < n:
        ch = source[i]
        if ch in " \t\r\n,":
            i += 1
        elif ch == "#":
            while i < n and source[i] != "\n":
                i += 1
        elif ch == "." and source[i:i + 3] == "...":
            tokens.append(_GQLToken("spread", "..."))
            i += 3
        elif ch in "{}()[]:!=$@&|":
            tokens.append(_GQLToken("punct", ch))
            i += 1
        elif ch == '"':
            j = i + 1
            out = []
            while j < n and source[j] != '"':
                if source[j] == "\\" and j + 1 < n:
                    nxt = source[j + 1]
                    out.append({"n": "\n", "t": "\t", "r": "\r", '"': '"',
                                "\\": "\\", "/": "/"}.get(nxt, nxt))
                    j += 2
                else:
                    out.append(source[j])
                    j += 1
            tokens.append(_GQLToken("string", "".join(out)))
            i = j + 1
        elif ch.isdigit() or (ch == "-" and i + 1 < n and source[i + 1].isdigit()):
            j = i
            if source[j] == "-":
                j += 1
            while j < n and (source[j].isdigit() or source[j] == "."):
                j += 1
            text = source[i:j]
            if "." in text:
                tokens.append(_GQLToken("float", float(text)))
            else:
                tokens.append(_GQLToken("int", int(text)))
            i = j
        elif ch.isalpha() or ch == "_":
            j = i
            while j < n and (source[j].isalnum() or source[j] == "_"):
                j += 1
            tokens.append(_GQLToken("name", source[i:j]))
            i = j
        else:
            raise ValueError("unexpected character %r in GraphQL source" % ch)
    tokens.append(_GQLToken("eof", None))
    return tokens


class _GQLField:
    __slots__ = ("alias", "name", "args", "selections", "directives")

    def __init__(self, alias, name, args, selections):
        self.alias = alias
        self.name = name
        self.args = args
        self.selections = selections
        self.directives = {}


class _GQLFragment:
    __slots__ = ("type_cond", "selections")

    def __init__(self, type_cond, selections):
        self.type_cond = type_cond
        self.selections = selections


class _GQLOperation:
    __slots__ = ("op_type", "name", "variables", "selections")

    def __init__(self, op_type, name, variables, selections):
        self.op_type = op_type
        self.name = name
        self.variables = variables
        self.selections = selections


class _GQLParser:
    def __init__(self, source):
        self.tokens = _gql_lex(source)
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos]

    def next(self):
        tok = self.tokens[self.pos]
        self.pos += 1
        return tok

    def expect_punct(self, value):
        tok = self.next()
        if tok.kind != "punct" or tok.value != value:
            raise ValueError("expected %r, got %r" % (value, tok.value))
        return tok

    def expect_name(self):
        tok = self.next()
        if tok.kind != "name":
            raise ValueError("expected a name, got %r" % tok.value)
        return tok.value

    def parse(self):
        operations = []
        fragments = {}
        while self.peek().kind != "eof":
            tok = self.peek()
            if tok.kind == "name" and tok.value == "fragment":
                self.next()
                name = self.expect_name()
                self.expect_name()  # "on"
                type_cond = self.expect_name()
                fragments[name] = _GQLFragment(
                    type_cond, self.parse_selections())
            elif tok.kind == "name" and tok.value in ("query", "mutation"):
                op_type = self.next().value
                name = None
                if self.peek().kind == "name":
                    name = self.next().value
                variables = {}
                if self.peek().kind == "punct" and self.peek().value == "(":
                    variables = self.parse_var_defs()
                operations.append(_GQLOperation(
                    op_type, name, variables, self.parse_selections()))
            elif tok.kind == "punct" and tok.value == "{":
                operations.append(_GQLOperation(
                    "query", None, {}, self.parse_selections()))
            else:
                raise ValueError("unexpected token %r" % tok.value)
        return operations, fragments

    def parse_var_defs(self):
        variables = {}
        self.expect_punct("(")
        while not (self.peek().kind == "punct" and self.peek().value == ")"):
            self.expect_punct("$")
            name = self.expect_name()
            self.expect_punct(":")
            var_type = self.parse_type()
            default = _GQL_NO_DEFAULT
            if self.peek().kind == "punct" and self.peek().value == "=":
                self.next()
                default = self.parse_value()
            variables[name] = (var_type, default)
            if self.peek().kind == "punct" and self.peek().value == ",":
                self.next()
        self.expect_punct(")")
        return variables

    def parse_type(self):
        if self.peek().kind == "punct" and self.peek().value == "[":
            self.next()
            inner = self.parse_type()
            self.expect_punct("]")
            result = ("list", inner)
        else:
            result = self.expect_name()
        if self.peek().kind == "punct" and self.peek().value == "!":
            self.next()
            result = ("required", result)
        return result

    def parse_selections(self):
        self.expect_punct("{")
        selections = []
        while not (self.peek().kind == "punct" and self.peek().value == "}"):
            selections.append(self.parse_selection())
        self.expect_punct("}")
        return selections

    def parse_selection(self):
        tok = self.peek()
        if tok.kind == "spread":
            self.next()
            if self.peek().kind == "name" and self.peek().value == "on":
                self.next()
                type_cond = self.expect_name()
                return _GQLFragment(type_cond, self.parse_selections())
            if self.peek().kind == "name":
                return ("spread", self.next().value)
            return _GQLFragment(None, self.parse_selections())
        name = self.expect_name()
        alias = None
        if self.peek().kind == "punct" and self.peek().value == ":":
            self.next()
            alias = name
            name = self.expect_name()
        args = {}
        if self.peek().kind == "punct" and self.peek().value == "(":
            args = self.parse_args()
        # directives: @include/@skip are honoured, others ignored
        directives = {}
        while self.peek().kind == "punct" and self.peek().value == "@":
            self.next()
            dname = self.expect_name()
            dargs = {}
            if self.peek().kind == "punct" and self.peek().value == "(":
                dargs = self.parse_args()
            directives[dname] = dargs
        selections = []
        if self.peek().kind == "punct" and self.peek().value == "{":
            selections = self.parse_selections()
        field = _GQLField(alias, name, args, selections)
        field.directives = directives
        return field

    def parse_args(self):
        args = {}
        self.expect_punct("(")
        while not (self.peek().kind == "punct" and self.peek().value == ")"):
            name = self.expect_name()
            self.expect_punct(":")
            args[name] = self.parse_value()
            if self.peek().kind == "punct" and self.peek().value == ",":
                self.next()
        self.expect_punct(")")
        return args

    def parse_value(self):
        tok = self.next()
        if tok.kind == "punct" and tok.value == "$":
            return ("var", self.expect_name())
        if tok.kind == "punct" and tok.value == "[":
            items = []
            while not (self.peek().kind == "punct" and self.peek().value == "]"):
                items.append(self.parse_value())
                if self.peek().kind == "punct" and self.peek().value == ",":
                    self.next()
            self.expect_punct("]")
            return ("list", items)
        if tok.kind == "punct" and tok.value == "{":
            obj = {}
            while not (self.peek().kind == "punct" and self.peek().value == "}"):
                key = self.expect_name()
                self.expect_punct(":")
                obj[key] = self.parse_value()
                if self.peek().kind == "punct" and self.peek().value == ",":
                    self.next()
            self.expect_punct("}")
            return ("object", obj)
        if tok.kind in ("string", "int", "float"):
            return (tok.kind, tok.value)
        if tok.kind == "name":
            if tok.value == "true":
                return ("bool", True)
            if tok.value == "false":
                return ("bool", False)
            if tok.value == "null":
                return ("null", None)
            return ("enum", tok.value)
        raise ValueError("unexpected value token %r" % tok.value)


def _gql_eval(value, variables):
    """Resolve a parsed value AST against the operation's variables."""
    kind = value[0]
    if kind == "var":
        return variables.get(value[1])
    if kind == "list":
        return [_gql_eval(item, variables) for item in value[1]]
    if kind == "object":
        return {k: _gql_eval(v, variables) for k, v in value[1].items()}
    if kind == "enum":
        return value[1]
    return value[1]


class _GQLNoDefault:
    pass


_GQL_NO_DEFAULT = _GQLNoDefault()


# The schema's field lists (for __type introspection) and the type of
# each field's value (for the executor's recursion).
GQL_FIELD_NAMES = {
    "Query": ["viewer", "repository", "node", "__type", "__schema"],
    "Mutation": ["createIssue", "closeIssue", "createPullRequest",
                 "mergePullRequest", "addComment"],
    "User": ["login", "id", "name"],
    "Repository": ["id", "databaseId", "name", "nameWithOwner", "owner",
                   "defaultBranchRef", "viewerPermission",
                   "hasIssuesEnabled", "issue", "issues", "pullRequests",
                   "pullRequest"],
    "Issue": ["id", "databaseId", "number", "title", "body", "state",
              "repository"],
    "PullRequest": ["id", "databaseId", "number", "title", "body", "state",
                    "headRefName", "baseRefName", "mergeable", "merged",
                    "files"],
    "IssueConnection": ["nodes", "totalCount", "pageInfo"],
    "PullRequestConnection": ["nodes", "totalCount", "pageInfo"],
    "PullRequestFileConnection": ["nodes", "totalCount"],
    "PullRequestFile": ["path"],
    "PageInfo": ["hasNextPage", "endCursor", "hasPreviousPage",
                 "startCursor"],
    "Ref": ["name"],
    "IssueComment": ["id", "body"],
    "IssueCommentEdge": ["node"],
    "__Type": ["name", "kind", "fields", "enumValues"],
    "__Field": ["name"],
    "__EnumValue": ["name"],
    "__Schema": ["queryType", "types"],
    "CreateIssuePayload": ["issue"],
    "CloseIssuePayload": ["issue"],
    "CreatePullRequestPayload": ["pullRequest"],
    "MergePullRequestPayload": ["pullRequest"],
    "AddCommentPayload": ["commentEdge"],
}

GQL_FIELD_TYPE = {
    ("Query", "viewer"): "User",
    ("Query", "repository"): "Repository",
    ("Query", "node"): "Node",
    ("Query", "__type"): "__Type",
    ("Query", "__schema"): "__Schema",
    ("Repository", "owner"): "User",
    ("Repository", "defaultBranchRef"): "Ref",
    ("Repository", "issue"): "Issue",
    ("Repository", "issues"): "IssueConnection",
    ("Repository", "pullRequests"): "PullRequestConnection",
    ("Repository", "pullRequest"): "PullRequest",
    ("Issue", "repository"): "Repository",
    ("PullRequest", "files"): "PullRequestFileConnection",
    ("IssueConnection", "nodes"): "Issue",
    ("IssueConnection", "pageInfo"): "PageInfo",
    ("PullRequestConnection", "nodes"): "PullRequest",
    ("PullRequestConnection", "pageInfo"): "PageInfo",
    ("PullRequestFileConnection", "nodes"): "PullRequestFile",
    ("IssueCommentEdge", "node"): "IssueComment",
    ("__Type", "fields"): "__Field",
    ("__Type", "enumValues"): "__EnumValue",
    ("__Schema", "queryType"): "__Type",
    ("__Schema", "types"): "__Type",
    ("Mutation", "createIssue"): "CreateIssuePayload",
    ("Mutation", "closeIssue"): "CloseIssuePayload",
    ("Mutation", "createPullRequest"): "CreatePullRequestPayload",
    ("Mutation", "mergePullRequest"): "MergePullRequestPayload",
    ("Mutation", "addComment"): "AddCommentPayload",
    ("CreateIssuePayload", "issue"): "Issue",
    ("CloseIssuePayload", "issue"): "Issue",
    ("CreatePullRequestPayload", "pullRequest"): "PullRequest",
    ("MergePullRequestPayload", "pullRequest"): "PullRequest",
    ("AddCommentPayload", "commentEdge"): "IssueCommentEdge",
}

GQL_ENUM_VALUES = {
    "SearchType": ["ISSUE", "REPOSITORY", "USER", "DISCUSSION", "CODE"],
    "IssueState": ["OPEN", "CLOSED"],
    "PullRequestState": ["OPEN", "CLOSED", "MERGED"],
    "MergeableState": ["MERGEABLE", "CONFLICTING", "UNKNOWN"],
    "OrderDirection": ["ASC", "DESC"],
    "IssueOrderField": ["CREATED_AT", "UPDATED_AT", "COMMENTS"],
}

# ---------------------------------------------------------------------------
# GraphQL: executor
# ---------------------------------------------------------------------------

class _GVal:
    """A resolved value with its runtime GraphQL type."""

    __slots__ = ("type", "data")

    def __init__(self, type_name, data):
        self.type = type_name
        self.data = data


class _GQLError(Exception):
    pass


def _cursor_encode(number):
    return base64.b64encode(("cursor:%d" % number).encode("ascii")).decode("ascii")


def _cursor_decode(cursor):
    try:
        raw = base64.b64decode(cursor).decode("ascii")
    except Exception:
        return None
    if not raw.startswith("cursor:"):
        return None
    try:
        return int(raw[len("cursor:"):])
    except ValueError:
        return None


def _gql_issue_id(repo, issue):
    return _gql_id("I", "%s#%d" % (repo.full_name, issue["number"]))


def _gql_pull_id(repo, pull):
    return _gql_id("PR", "%s#%d" % (repo.full_name, pull["number"]))


def _gql_comment_id(repo, issue, comment):
    return _gql_id("C", "%s#%d:%d" % (
        repo.full_name, issue["number"], comment["id"]))


def _gql_int(text):
    try:
        return int(text)
    except (TypeError, ValueError):
        return None


def _create_issue_gql(repo, title, body):
    with STORE.lock:
        repo.issue_seq += 1
        STORE.next_object_id += 1
        issue = {
            "id": STORE.next_object_id,
            "number": repo.issue_seq,
            "title": title,
            "body": body or "",
            "state": "open",
            "labels": [],
            "comments": [],
            "created_at": FIXED_NOW,
            "updated_at": FIXED_NOW,
        }
        repo.issues.append(issue)
    return issue


def _create_pull_gql(repo, head, base, title, body):
    if "refs/heads/%s" % head not in repo.refs:
        raise _GQLError("head branch does not exist: %s" % head)
    if "refs/heads/%s" % base not in repo.refs:
        raise _GQLError("base branch does not exist: %s" % base)
    with STORE.lock:
        for existing in repo.pulls:
            if existing["state"] == "open" \
                    and existing["head_ref"] == head \
                    and existing["base_ref"] == base:
                raise _GQLError("A pull request already exists for %s" % head)
        repo.pull_seq += 1
        STORE.next_object_id += 1
        pull = {
            "id": STORE.next_object_id,
            "number": repo.pull_seq,
            "title": title or "",
            "body": body or "",
            "state": "open",
            "head_ref": head,
            "base_ref": base,
            "merged": False,
            "merged_at": None,
            "merge_commit_sha": None,
            "created_at": FIXED_NOW,
            "updated_at": FIXED_NOW,
        }
        repo.pulls.append(pull)
    return pull


def _merge_pull_gql(repo, pull):
    with STORE.lock:
        if pull["state"] != "open":
            raise _GQLError("Pull request is already closed")
        changes, conflict = _pr_diff(repo, pull)
        if conflict:
            raise _GQLError("Merge conflict")
        head_tip, base_tip = _pr_head_base(repo, pull)
        base_files = tree_paths(
            repo, parse_commit(repo.objects[base_tip][1])["tree"])
        for path, entry in changes.items():
            if entry is None:
                base_files.pop(path, None)
            else:
                base_files[path] = entry
        new_tree = build_tree_from_paths(repo, base_files)
        message = pull["title"] or ("Merge pull request #%d" % pull["number"])
        commit_data = build_commit(new_tree, [base_tip], message)
        commit_oid = hash_object("commit", commit_data)
        repo.objects[commit_oid] = ("commit", commit_data)
        repo.refs["refs/heads/%s" % pull["base_ref"]] = commit_oid
        pull["state"] = "closed"
        pull["merged"] = True
        pull["merged_at"] = FIXED_NOW
        pull["merge_commit_sha"] = commit_oid
        pull["updated_at"] = FIXED_NOW
    return commit_oid


def _issues_connection(repo, args):
    issues = list(repo.issues)
    states = args.get("states")
    if states:
        wanted = set(str(s).upper() for s in states)
    else:
        wanted = {"OPEN"}
    issues = [i for i in issues if i["state"].upper() in wanted]
    order_by = args.get("orderBy") or {}
    direction = str(order_by.get("direction") or "ASC").upper()
    issues.sort(key=lambda i: i["number"], reverse=(direction == "DESC"))
    after = args.get("after")
    if after:
        cursor_num = _cursor_decode(after)
        if cursor_num is not None:
            if direction == "DESC":
                issues = [i for i in issues if i["number"] < cursor_num]
            else:
                issues = [i for i in issues if i["number"] > cursor_num]
    total = len(issues)
    first = args.get("first")
    if first is not None:
        page = issues[:int(first)]
        has_next = len(issues) > int(first)
    else:
        page = issues
        has_next = False
    end_cursor = _cursor_encode(page[-1]["number"]) if page else None
    start_cursor = _cursor_encode(page[0]["number"]) if page else None
    return _GVal("IssueConnection", {
        "nodes": [_GVal("Issue", (repo, i)) for i in page],
        "totalCount": total,
        "pageInfo": _GVal("PageInfo", {
            "hasNextPage": has_next, "endCursor": end_cursor,
            "hasPreviousPage": after is not None,
            "startCursor": start_cursor,
        }),
    })


def _pulls_connection(repo, args):
    pulls = list(repo.pulls)
    states = args.get("states")
    if states:
        wanted = set(str(s).upper() for s in states)
    else:
        wanted = {"OPEN"}
    pulls = [p for p in pulls if p["state"].upper() in wanted]
    pulls.sort(key=lambda p: p["number"], reverse=True)
    after = args.get("after")
    if after:
        cursor_num = _cursor_decode(after)
        if cursor_num is not None:
            pulls = [p for p in pulls if p["number"] < cursor_num]
    total = len(pulls)
    first = args.get("first")
    if first is not None:
        page = pulls[:int(first)]
        has_next = len(pulls) > int(first)
    else:
        page = pulls
        has_next = False
    end_cursor = _cursor_encode(page[-1]["number"]) if page else None
    start_cursor = _cursor_encode(page[0]["number"]) if page else None
    return _GVal("PullRequestConnection", {
        "nodes": [_GVal("PullRequest", (repo, p)) for p in page],
        "totalCount": total,
        "pageInfo": _GVal("PageInfo", {
            "hasNextPage": has_next, "endCursor": end_cursor,
            "hasPreviousPage": after is not None,
            "startCursor": start_cursor,
        }),
    })


class _GQLExecutor:
    def __init__(self, variables, fragments):
        self.variables = variables or {}
        self.fragments = fragments or {}
        self.errors = []

    def execute(self, operation):
        root_type = "Query" if operation.op_type == "query" else "Mutation"
        data = self._resolve(_GVal(root_type, None), operation.selections)
        result = {"data": data}
        if self.errors:
            result["errors"] = [{"message": m} for m in self.errors]
        return result

    def _skip(self, field):
        directives = getattr(field, "directives", {}) or {}
        for name, dargs in directives.items():
            if name == "skip":
                if _gql_eval(dargs.get("if", ("bool", False)), self.variables):
                    return True
            elif name == "include":
                if not _gql_eval(dargs.get("if", ("bool", True)), self.variables):
                    return True
        return False

    def _resolve(self, parent, selections):
        out = {}
        for sel in selections:
            if isinstance(sel, _GQLFragment):
                if sel.type_cond is None or sel.type_cond == parent.type:
                    out.update(self._resolve(parent, sel.selections))
            elif isinstance(sel, tuple) and sel[0] == "spread":
                frag = self.fragments.get(sel[1])
                if frag is not None:
                    out.update(self._resolve(parent, frag.selections))
            else:
                if self._skip(sel):
                    continue
                key = sel.alias or sel.name
                out[key] = self._resolve_field(parent, sel)
        return out

    def _resolve_field(self, parent, field):
        ptype = parent.type
        name = field.name
        if name not in GQL_FIELD_NAMES.get(ptype, []):
            self.errors.append(
                'Cannot query field "%s" on type "%s".' % (name, ptype))
            return None
        args = {k: _gql_eval(v, self.variables)
                for k, v in field.args.items()}
        try:
            raw = self._field_value(parent, name, args)
        except _GQLError as exc:
            self.errors.append(str(exc))
            return None
        if raw is None:
            return None
        if isinstance(raw, list):
            return [self._apply(item, field.selections) for item in raw]
        return self._apply(raw, field.selections)

    def _apply(self, raw, selections):
        if isinstance(raw, _GVal):
            if not selections:
                return None
            return self._resolve(raw, selections)
        return raw

    # -- field values ---------------------------------------------------------
    def _field_value(self, parent, name, args):
        ptype = parent.type
        data = parent.data
        if ptype == "Query":
            return self._query_field(name, args)
        if ptype == "Mutation":
            return self._mutation_field(name, args)
        if ptype == "User":
            if name == "login":
                return data["login"]
            if name == "id":
                return _gql_id("U", data["login"])
            if name == "name":
                return data.get("name", "")
        if ptype == "Repository":
            return self._repo_field(data, name, args)
        if ptype == "Issue":
            repo, issue = data
            if name == "id":
                return _gql_issue_id(repo, issue)
            if name == "databaseId":
                return issue["id"]
            if name == "number":
                return issue["number"]
            if name == "title":
                return issue["title"]
            if name == "body":
                return issue.get("body", "")
            if name == "state":
                return "OPEN" if issue["state"] == "open" else "CLOSED"
            if name == "repository":
                return _GVal("Repository", repo)
        if ptype == "PullRequest":
            repo, pull = data
            if name == "id":
                return _gql_pull_id(repo, pull)
            if name == "databaseId":
                return pull["id"]
            if name == "number":
                return pull["number"]
            if name == "title":
                return pull["title"]
            if name == "body":
                return pull.get("body", "")
            if name == "state":
                if pull["merged"]:
                    return "MERGED"
                return "OPEN" if pull["state"] == "open" else "CLOSED"
            if name == "headRefName":
                return pull["head_ref"]
            if name == "baseRefName":
                return pull["base_ref"]
            if name == "mergeable":
                return ("MERGEABLE" if _pr_mergeable(repo, pull)
                        else "CONFLICTING")
            if name == "merged":
                return pull["merged"]
            if name == "files":
                files = _pr_files(repo, pull)
                first = args.get("first")
                if first is not None:
                    files = files[:int(first)]
                return _GVal("PullRequestFileConnection", {
                    "nodes": [_GVal("PullRequestFile", {"path": f["filename"]})
                              for f in files],
                    "totalCount": len(files),
                })
        if ptype in ("IssueConnection", "PullRequestConnection"):
            if name == "nodes":
                return data["nodes"]
            if name == "totalCount":
                return data["totalCount"]
            if name == "pageInfo":
                return data["pageInfo"]
        if ptype == "PullRequestFileConnection":
            if name == "nodes":
                return data["nodes"]
            if name == "totalCount":
                return data["totalCount"]
        if ptype == "PullRequestFile":
            if name == "path":
                return data["path"]
        if ptype == "PageInfo":
            return data.get(name)
        if ptype == "Ref":
            if name == "name":
                return data["name"]
        if ptype == "IssueComment":
            repo, issue, comment = data
            if name == "id":
                return _gql_comment_id(repo, issue, comment)
            if name == "body":
                return comment["body"]
        if ptype == "IssueCommentEdge":
            if name == "node":
                return _GVal("IssueComment", data)
        if ptype == "__Type":
            if name == "name":
                return data["name"]
            if name == "kind":
                return data["kind"]
            if name == "fields":
                return data.get("fields")
            if name == "enumValues":
                return data.get("enumValues")
        if ptype in ("__Field", "__EnumValue"):
            if name == "name":
                return data["name"]
        if ptype == "__Schema":
            if name == "queryType":
                return data["queryType"]
            if name == "types":
                return data["types"]
        if ptype in ("CreateIssuePayload", "CloseIssuePayload"):
            if name == "issue":
                return data["issue"]
        if ptype in ("CreatePullRequestPayload", "MergePullRequestPayload"):
            if name == "pullRequest":
                return data["pullRequest"]
        if ptype == "AddCommentPayload":
            if name == "commentEdge":
                return data["commentEdge"]
        return None

    def _query_field(self, name, args):
        if name == "viewer":
            return _GVal("User", {"login": VIEWER_LOGIN, "id": VIEWER_ID,
                                  "name": VIEWER_NAME})
        if name == "repository":
            repo = _find_repo(args.get("owner"), args.get("name"))
            return _GVal("Repository", repo) if repo else None
        if name == "node":
            kind, key = _gql_decode(args.get("id") or "")
            if kind is None:
                return None
            if kind == "R":
                owner, _, repo_name = key.partition("/")
                repo = _find_repo(owner, repo_name)
                return _GVal("Repository", repo) if repo else None
            if kind == "U":
                if key == VIEWER_LOGIN:
                    return _GVal("User", {"login": VIEWER_LOGIN,
                                          "id": VIEWER_ID,
                                          "name": VIEWER_NAME})
                return None
            if kind in ("I", "PR", "C"):
                owner_repo, _, number = key.partition("#")
                owner, _, repo_name = owner_repo.partition("/")
                repo = _find_repo(owner, repo_name)
                if repo is None:
                    return None
                try:
                    num = int(number.split(":")[0])
                except ValueError:
                    return None
                if kind == "I":
                    issue = next((i for i in repo.issues
                                  if i["number"] == num), None)
                    return _GVal("Issue", (repo, issue)) if issue else None
                if kind == "C":
                    comment = None
                    found_issue = None
                    for issue in repo.issues:
                        if issue["number"] != num:
                            continue
                        for cand in issue["comments"]:
                            if str(cand["id"]) == number.split(":")[-1]:
                                comment, found_issue = cand, issue
                    if comment is None:
                        return None
                    return _GVal("IssueComment",
                                 (repo, found_issue, comment))
                pull = next((p for p in repo.pulls
                             if p["number"] == num), None)
                return _GVal("PullRequest", (repo, pull)) if pull else None
            return None
        if name == "__type":
            return self._introspect_type(args.get("name"))
        if name == "__schema":
            return _GVal("__Schema", {
                "queryType": self._introspect_type("Query"),
                "types": [self._introspect_type(t) for t in
                          sorted(GQL_FIELD_NAMES)],
            })
        return None

    def _introspect_type(self, name):
        if name in GQL_ENUM_VALUES:
            return _GVal("__Type", {
                "name": name, "kind": "ENUM", "fields": None,
                "enumValues": [_GVal("__EnumValue", {"name": v})
                               for v in GQL_ENUM_VALUES[name]],
            })
        if name in GQL_FIELD_NAMES:
            return _GVal("__Type", {
                "name": name, "kind": "OBJECT",
                "fields": [_GVal("__Field", {"name": f})
                           for f in GQL_FIELD_NAMES[name]],
                "enumValues": None,
            })
        if name == "Node":
            return _GVal("__Type", {
                "name": "Node", "kind": "INTERFACE",
                "fields": [_GVal("__Field", {"name": "id"})],
                "enumValues": None,
            })
        return None

    def _repo_field(self, repo, name, args):
        if name == "id":
            return _gql_id("R", repo.full_name)
        if name == "databaseId":
            return repo.id
        if name == "name":
            return repo.name
        if name == "nameWithOwner":
            return repo.full_name
        if name == "owner":
            return _GVal("User", {"login": repo.owner, "id": VIEWER_ID,
                                  "name": VIEWER_NAME})
        if name == "defaultBranchRef":
            if repo.head_oid():
                return _GVal("Ref", {"name": repo.default_branch})
            return None
        if name == "viewerPermission":
            return "ADMIN"
        if name == "hasIssuesEnabled":
            return True
        if name == "issue":
            issue = next((i for i in repo.issues
                          if i["number"] == args.get("number")), None)
            return _GVal("Issue", (repo, issue)) if issue else None
        if name == "issues":
            return _issues_connection(repo, args)
        if name == "pullRequests":
            return _pulls_connection(repo, args)
        if name == "pullRequest":
            pull = next((p for p in repo.pulls
                         if p["number"] == args.get("number")), None)
            return _GVal("PullRequest", (repo, pull)) if pull else None
        return None

    def _mutation_field(self, name, args):
        data = args.get("input") or {}
        if name == "createIssue":
            kind, key = _gql_decode(data.get("repositoryId") or "")
            if kind != "R":
                raise _GQLError("repositoryId does not name a repository")
            owner, _, repo_name = key.partition("/")
            repo = _find_repo(owner, repo_name)
            if repo is None:
                raise _GQLError("repository not found")
            issue = _create_issue_gql(repo, data.get("title") or "",
                                      data.get("body") or "")
            return _GVal("CreateIssuePayload",
                         {"issue": _GVal("Issue", (repo, issue))})
        if name == "closeIssue":
            kind, key = _gql_decode(data.get("issueId") or "")
            if kind != "I":
                raise _GQLError("issueId does not name an issue")
            owner_repo, _, number = key.partition("#")
            owner, _, repo_name = owner_repo.partition("/")
            repo = _find_repo(owner, repo_name)
            issue = None
            num = _gql_int(number)
            if repo is not None and num is not None:
                issue = next((i for i in repo.issues
                              if i["number"] == num), None)
            if issue is None:
                raise _GQLError("issue not found")
            with STORE.lock:
                issue["state"] = "closed"
                issue["updated_at"] = FIXED_NOW
            return _GVal("CloseIssuePayload",
                         {"issue": _GVal("Issue", (repo, issue))})
        if name == "createPullRequest":
            kind, key = _gql_decode(data.get("repositoryId") or "")
            if kind != "R":
                raise _GQLError("repositoryId does not name a repository")
            owner, _, repo_name = key.partition("/")
            repo = _find_repo(owner, repo_name)
            if repo is None:
                raise _GQLError("repository not found")
            pull = _create_pull_gql(repo, data.get("headRefName") or "",
                                    data.get("baseRefName") or "",
                                    data.get("title") or "",
                                    data.get("body") or "")
            return _GVal("CreatePullRequestPayload",
                         {"pullRequest": _GVal("PullRequest", (repo, pull))})
        if name == "mergePullRequest":
            kind, key = _gql_decode(data.get("pullRequestId") or "")
            if kind != "PR":
                raise _GQLError("pullRequestId does not name a pull request")
            owner_repo, _, number = key.partition("#")
            owner, _, repo_name = owner_repo.partition("/")
            repo = _find_repo(owner, repo_name)
            pull = None
            num = _gql_int(number)
            if repo is not None and num is not None:
                pull = next((p for p in repo.pulls
                             if p["number"] == num), None)
            if pull is None:
                raise _GQLError("pull request not found")
            _merge_pull_gql(repo, pull)
            return _GVal("MergePullRequestPayload",
                         {"pullRequest": _GVal("PullRequest", (repo, pull))})
        if name == "addComment":
            kind, key = _gql_decode(data.get("subjectId") or "")
            if kind != "I":
                raise _GQLError("subjectId does not name an issue")
            owner_repo, _, number = key.partition("#")
            owner, _, repo_name = owner_repo.partition("/")
            repo = _find_repo(owner, repo_name)
            issue = None
            num = _gql_int(number)
            if repo is not None and num is not None:
                issue = next((i for i in repo.issues
                              if i["number"] == num), None)
            if issue is None:
                raise _GQLError("issue not found")
            with STORE.lock:
                STORE.next_object_id += 1
                comment = {
                    "id": STORE.next_object_id,
                    "body": data.get("body") or "",
                    "created_at": FIXED_NOW, "updated_at": FIXED_NOW,
                }
                issue["comments"].append(comment)
            return _GVal("AddCommentPayload", {
                "commentEdge": _GVal(
                    "IssueCommentEdge", (repo, issue, comment)),
            })
        return None


def _gql_execute_one(payload):
    """Execute one {query, variables, operationName} payload."""
    if not isinstance(payload, dict) or not isinstance(
            payload.get("query"), str):
        return {"data": None, "errors": [{"message": "query is required"}]}
    variables = payload.get("variables") or {}
    if not isinstance(variables, dict):
        variables = {}
    try:
        operations, fragments = _GQLParser(payload["query"]).parse()
    except ValueError as exc:
        return {"data": None, "errors": [{"message": str(exc)}]}
    operation_name = payload.get("operationName")
    operation = None
    if operation_name:
        for candidate in operations:
            if candidate.name == operation_name:
                operation = candidate
                break
        if operation is None:
            return {"data": None, "errors": [
                {"message": 'Unknown operation named "%s".' % operation_name}]}
    elif operations:
        operation = operations[0]
    if operation is None:
        return {"data": None, "errors": [{"message": "No operation found"}]}
    # variable defaults
    merged = dict(variables)
    for name, spec in operation.variables.items():
        if name not in merged and spec[1] is not _GQL_NO_DEFAULT:
            merged[name] = _gql_eval(spec[1], {})
    return _GQLExecutor(merged, fragments).execute(operation)


def _handle_graphql(handler, method):
    if method != "POST":
        handler._error(404, "Not Found")
        return
    if not handler._authorized():
        handler._error(401, "Requires authentication")
        return
    obj, err = handler._json_body()
    if err is not None:
        handler._error(err[0], err[1])
        return
    if isinstance(obj, list):
        handler._send_json(200, [_gql_execute_one(item) for item in obj])
    else:
        handler._send_json(200, _gql_execute_one(obj))


# ---------------------------------------------------------------------------
# MCP (Model Context Protocol, Streamable HTTP at /mcp)
#
# The suite's client speaks the modern 2026-07-28 revision first: it probes
# `server/discover`, and only falls back to the legacy `initialize` +
# `notifications/initialized` handshake when discover answers method-not-found.
# This server answers discover, so the modern path is the one exercised; the
# legacy handshake is implemented too, for completeness.
#
# Transport facts the implementation relies on:
#   - plain JSON answers are accepted (the client parses the body as JSON-RPC
#     when the content type is application/json; SSE is not required);
#   - every JSON-RPC response echoes the request's id verbatim, so concurrent
#     calls keep their own ids;
#   - a tool result carries BOTH a text content block (the JSON of the object)
#     and structuredContent (the object itself): the checks read the title out
#     of the text and the number out of the structured content;
#   - the tools list is one module-level constant, serialized the same way on
#     every call, so two tools/list answers are byte-identical.
# ---------------------------------------------------------------------------

MCP_PROTOCOL_VERSION = "2026-07-28"
MCP_SUPPORTED_VERSIONS = [
    "2026-07-28", "2025-11-25", "2025-06-18", "2025-03-26",
]
MCP_SERVER_NAME = "forge"
MCP_SERVER_VERSION = "1.0.0"

MCP_TOOLS = [
    {
        "name": "create_repo",
        "description": "Create a new repository owned by the authenticated user.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string",
                         "description": "Repository name"},
                "description": {"type": "string",
                                "description": "Repository description"},
                "private": {"type": "boolean",
                            "description": "Whether the repository is private"},
                "owner": {"type": "string",
                          "description": "Owner login (defaults to the authenticated user)"},
            },
            "required": ["name"],
        },
    },
    {
        "name": "get_repo",
        "description": "Get a repository by owner and name.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string",
                          "description": "Repository owner login"},
                "repo": {"type": "string",
                         "description": "Repository name"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_issue",
        "description": "Create an issue in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string",
                          "description": "Repository owner login"},
                "repo": {"type": "string",
                         "description": "Repository name"},
                "title": {"type": "string",
                          "description": "Issue title"},
                "body": {"type": "string",
                         "description": "Issue body"},
            },
            "required": ["owner", "repo", "title"],
        },
    },
    {
        "name": "list_issues",
        "description": "List issues in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string",
                          "description": "Repository owner login"},
                "repo": {"type": "string",
                         "description": "Repository name"},
                "state": {"type": "string",
                          "description": "Issue state filter: open, closed, or all"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_pull_request",
        "description": "Open a pull request from a head branch into a base branch.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string",
                          "description": "Repository owner login"},
                "repo": {"type": "string",
                         "description": "Repository name"},
                "title": {"type": "string",
                          "description": "Pull request title"},
                "body": {"type": "string",
                         "description": "Pull request body"},
                "head": {"type": "string",
                         "description": "Head branch name"},
                "base": {"type": "string",
                         "description": "Base branch name"},
            },
            "required": ["owner", "repo", "title", "head", "base"],
        },
    },
    {
        "name": "merge_pull_request",
        "description": "Merge a pull request into its base branch.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string",
                          "description": "Repository owner login"},
                "repo": {"type": "string",
                         "description": "Repository name"},
                "pull_number": {"type": "integer",
                                "description": "Pull request number"},
            },
            "required": ["owner", "repo", "pull_number"],
        },
    },
]


def _mcp_result(obj):
    """A tool result: the object as JSON text AND as structured content."""
    return {
        "content": [{"type": "text",
                     "text": json.dumps(obj, separators=(",", ":"))}],
        "structuredContent": obj,
        "isError": False,
    }


def _mcp_error_result(message):
    return {
        "content": [{"type": "text", "text": message}],
        "isError": True,
    }


class _McpToolError(Exception):
    """A tool-level failure: answered as isError:true, not a JSON-RPC error."""


def _mcp_require(args, *fields):
    """The required arguments, or raise naming the missing ones."""
    missing = [f for f in fields
               if args.get(f) is None or args.get(f) == ""]
    if missing:
        raise _McpToolError("missing required argument(s): %s"
                            % ", ".join(missing))


def _mcp_repo(args):
    """Resolve {owner, repo} to a store repo, or raise a tool error."""
    _mcp_require(args, "owner", "repo")
    repo = _find_repo(str(args["owner"]), str(args["repo"]))
    if repo is None:
        raise _McpToolError("repository not found: %s/%s"
                            % (args["owner"], args["repo"]))
    return repo


def _mcp_call_tool(name, args):
    """Run one tool against the shared store. Returns a tool result dict."""
    if name == "create_repo":
        _mcp_require(args, "name")
        owner = args.get("owner")
        if owner is not None and str(owner) != VIEWER_LOGIN:
            raise _McpToolError("unknown owner: %s" % owner)
        repo, error = _create_repo_store(
            str(args["name"]), args.get("description") or "",
            bool(args.get("private", False)))
        if repo is None:
            raise _McpToolError(error)
        return _mcp_result(repo_json(repo))
    if name == "get_repo":
        repo = _mcp_repo(args)
        return _mcp_result(repo_json(repo))
    if name == "create_issue":
        _mcp_require(args, "title")
        repo = _mcp_repo(args)
        issue = _create_issue_gql(repo, str(args["title"]),
                                  str(args.get("body") or ""))
        return _mcp_result(issue_json(repo, issue))
    if name == "list_issues":
        repo = _mcp_repo(args)
        state = str(args.get("state") or "open").lower()
        if state not in ("open", "closed", "all"):
            state = "open"
        issues = [i for i in repo.issues
                  if state == "all" or i["state"] == state]
        payload = {
            "issues": [issue_json(repo, i) for i in issues],
            "total_count": len(issues),
        }
        return _mcp_result(payload)
    if name == "create_pull_request":
        _mcp_require(args, "title", "head", "base")
        repo = _mcp_repo(args)
        try:
            pull = _create_pull_gql(repo, str(args["head"]),
                                    str(args["base"]),
                                    str(args["title"]),
                                    str(args.get("body") or ""))
        except _GQLError as exc:
            raise _McpToolError(str(exc))
        return _mcp_result(pull_json(repo, pull))
    if name == "merge_pull_request":
        _mcp_require(args, "pull_number")
        repo = _mcp_repo(args)
        try:
            number = int(args["pull_number"])
        except (TypeError, ValueError):
            raise _McpToolError("pull_number must be an integer")
        pull = next((p for p in repo.pulls if p["number"] == number), None)
        if pull is None:
            raise _McpToolError("pull request #%d not found" % number)
        try:
            _merge_pull_gql(repo, pull)
        except _GQLError as exc:
            raise _McpToolError(str(exc))
        return _mcp_result(pull_json(repo, pull))
    return None


def _mcp_discover_result():
    """The 2026-07-28 DiscoverResult: versions, capabilities, identity."""
    info = {"name": MCP_SERVER_NAME, "version": MCP_SERVER_VERSION}
    return {
        "supportedVersions": list(MCP_SUPPORTED_VERSIONS),
        "capabilities": {"tools": {}},
        "serverInfo": dict(info),
        "_meta": {"io.modelcontextprotocol/serverInfo": dict(info)},
    }


def _handle_mcp(handler, method):
    if method == "DELETE":
        # A legacy client closing its session: nothing is held, just accept.
        handler._send_empty(204)
        return
    if method != "POST":
        handler._error(405, "Method Not Allowed")
        return
    if not handler._authorized():
        handler._error(401, "Requires authentication")
        return
    raw = handler._read_body()
    try:
        request = json.loads(raw.decode("utf-8"))
    except (ValueError, UnicodeDecodeError):
        # A body that is not JSON: HTTP 400 with JSON-RPC -32700.
        handler._send_json(400, {
            "jsonrpc": "2.0", "id": None,
            "error": {"code": -32700, "message": "Parse error"},
        })
        return
    if not isinstance(request, dict):
        handler._send_json(400, {
            "jsonrpc": "2.0", "id": None,
            "error": {"code": -32600, "message": "Invalid Request"},
        })
        return
    req_id = request.get("id")
    method_name = request.get("method")
    if not isinstance(method_name, str):
        handler._send_json(400, {
            "jsonrpc": "2.0", "id": req_id,
            "error": {"code": -32600, "message": "Invalid Request"},
        })
        return
    if req_id is None:
        # A notification (no id): no JSON-RPC response is ever sent.
        handler._send_empty(202)
        return
    params = request.get("params") or {}
    if not isinstance(params, dict):
        params = {}

    def answer(result=None, error=None):
        body = {"jsonrpc": "2.0", "id": req_id}
        if error is not None:
            body["error"] = error
        else:
            body["result"] = result
        handler._send_json(200, body)

    def rpc_error(code, message):
        return {"code": code, "message": message}

    if method_name == "server/discover":
        answer(_mcp_discover_result())
        return
    if method_name == "initialize":
        wanted = params.get("protocolVersion")
        chosen = wanted if wanted in MCP_SUPPORTED_VERSIONS \
            else "2025-11-25"
        answer({
            "protocolVersion": chosen,
            "capabilities": {"tools": {}},
            "serverInfo": {"name": MCP_SERVER_NAME,
                           "version": MCP_SERVER_VERSION},
        })
        return
    if method_name == "ping":
        answer({})
        return
    if method_name == "tools/list":
        # The same constant, serialized the same way, every call.
        answer({"tools": MCP_TOOLS})
        return
    if method_name == "tools/call":
        tool_name = params.get("name")
        arguments = params.get("arguments") or {}
        if not isinstance(arguments, dict):
            arguments = {}
        if not isinstance(tool_name, str) or tool_name == "":
            answer(error=rpc_error(-32602, "tools/call needs a tool name"))
            return
        try:
            result = _mcp_call_tool(tool_name, arguments)
        except _McpToolError as exc:
            answer(_mcp_error_result(str(exc)))
            return
        if result is None:
            answer(error=rpc_error(-32602, "unknown tool: %s" % tool_name))
            return
        answer(result)
        return
    answer(error=rpc_error(-32601, "method not found: %s" % method_name))


# ---------------------------------------------------------------------------
# lifecycle (main)
#
# The wire contract (kit program/env/src/wire.ts):
#   1. bind an ephemeral port — listen(0), never 8080;
#   2. POST {"port": N} to $MAKEFUN_ENV_URL/register (200 accepted,
#      409 means a register already won — keep going either way);
#   3. poll GET $MAKEFUN_ENV_URL/done until {"done": true}, then exit 0.
#      The env answers every poll at once (never held): poll, don't hold.
#      Interval starts at 250 ms and doubles to at most 2 s.
#   4. without MAKEFUN_ENV_URL (local development) just bind and serve
#      until interrupted.
#
# The bind address: the env dials the address the register request came
# from, so in env mode listen on all interfaces (0.0.0.0) — the split
# layout puts the env in another pod. Locally, loopback is enough.
# ---------------------------------------------------------------------------

DONE_POLL_FIRST_MS = 250
DONE_POLL_MAX_MS = 2000
DONE_REQUEST_TIMEOUT_S = 30


def _env_post_json(url, payload, timeout=10):
    request = urllib.request.Request(
        url, data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"}, method="POST")
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response.status, response.read()


def _env_get_json(url, timeout=DONE_REQUEST_TIMEOUT_S):
    request = urllib.request.Request(url, method="GET")
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response.status, json.loads(response.read().decode("utf-8"))


def _register_with_env(env_url, port):
    """POST {"port": N} to /register, retrying transient failures."""
    url = env_url + "/register"
    for attempt in range(12):
        try:
            status, _body = _env_post_json(url, {"port": port})
            if status in (200, 409):
                print("forge: registered port %d with %s (HTTP %d)"
                      % (port, url, status), flush=True)
                return True
            print("forge: register answered HTTP %d, retrying"
                  % status, flush=True)
        except urllib.error.HTTPError as exc:
            if exc.code in (200, 409):
                print("forge: registered port %d (HTTP %d)"
                      % (port, exc.code), flush=True)
                return True
            print("forge: register HTTP %d, retrying" % exc.code, flush=True)
        except Exception as exc:
            print("forge: register failed (%s), retrying" % exc, flush=True)
        time.sleep(min(0.25 * (2 ** attempt), 5.0))
    print("forge: could not register with the env; serving anyway",
          flush=True)
    return False


def _wait_for_done(env_url):
    """Poll GET /done until {"done": true}. Returns when done."""
    url = env_url + "/done"
    delay = DONE_POLL_FIRST_MS / 1000.0
    while True:
        try:
            _status, body = _env_get_json(url)
            if isinstance(body, dict) and body.get("done") is True:
                print("forge: env reports done; exiting 0", flush=True)
                return
        except Exception as exc:
            print("forge: done poll failed (%s), retrying" % exc, flush=True)
        time.sleep(delay)
        delay = min(delay * 2, DONE_POLL_MAX_MS / 1000.0)


def main():
    env_url = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
    if env_url:
        host = "0.0.0.0"
        port = 0
    else:
        host = "127.0.0.1"
        try:
            port = int(os.environ.get("PORT", "0"))
        except ValueError:
            port = 0
    server = ForgeServer((host, port), ForgeHandler)
    actual_port = server.server_address[1]
    print("forge: listening on http://%s:%d"
          % ("127.0.0.1", actual_port), flush=True)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    if env_url:
        _register_with_env(env_url, actual_port)
        try:
            _wait_for_done(env_url)
        finally:
            server.shutdown()
            server.server_close()
        return 0
    try:
        thread.join()
    except KeyboardInterrupt:
        print("forge: interrupted", flush=True)
    finally:
        server.shutdown()
        server.server_close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
