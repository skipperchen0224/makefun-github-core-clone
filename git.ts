// git.ts — pure-stdlib git object model and pack protocol.
// No git binary, no dependencies: node:crypto for SHA-1, node:zlib for pack streams.
// Plain JavaScript in a .ts file so Node 22's type stripping runs it as-is.

import { createHash } from 'node:crypto';
import * as zlib from 'node:zlib';

export const ZERO_OID = '0'.repeat(40);
const HEX40 = /^[0-9a-f]{40}$/;

export function isOid(v) {
  return typeof v === 'string' && HEX40.test(v);
}

export function sha1Hex(data) {
  return createHash('sha1').update(data).digest('hex');
}

/** The git object id of `type` + `data` ("<type> <size>\0<data>"). */
export function hashObject(type, data) {
  const buf = Buffer.isBuffer(data) ? data : Buffer.from(data);
  const header = Buffer.from(`${type} ${buf.length}\0`, 'ascii');
  return sha1Hex(Buffer.concat([header, buf]));
}

/** One tree entry: {mode, name, oid}. */
export function parseTree(data) {
  const entries = [];
  let off = 0;
  const buf = Buffer.isBuffer(data) ? data : Buffer.from(data);
  while (off < buf.length) {
    const sp = buf.indexOf(0x20, off);
    if (sp < 0) throw new Error('tree entry has no space');
    const mode = buf.toString('ascii', off, sp);
    const nul = buf.indexOf(0x00, sp);
    if (nul < 0) throw new Error('tree entry has no NUL');
    const name = buf.toString('utf8', sp + 1, nul);
    const oid = buf.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    off = nul + 21;
  }
  return entries;
}

/** Tree entries sorted the way git sorts them (directories sort as if named "name/"). */
function treeSortKey(entry) {
  return entry.mode === '40000' ? `${entry.name}/` : entry.name;
}

export function buildTree(entries) {
  const sorted = [...entries].sort((a, b) => {
    const ka = treeSortKey(a);
    const kb = treeSortKey(b);
    return ka < kb ? -1 : ka > kb ? 1 : 0;
  });
  const parts = [];
  for (const e of sorted) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

/** {tree, parents[], author, committer, message} from raw commit bytes. */
export function parseCommit(data) {
  const text = Buffer.isBuffer(data) ? data.toString('utf8') : data;
  const headEnd = text.indexOf('\n\n');
  const head = headEnd < 0 ? text : text.slice(0, headEnd);
  const message = headEnd < 0 ? '' : text.slice(headEnd + 2);
  let tree = '';
  const parents = [];
  let author = '';
  let committer = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
  }
  return { tree, parents, author, committer, message };
}

export function buildCommit({ tree, parents, author, committer, message }) {
  let out = `tree ${tree}\n`;
  for (const p of parents) out += `parent ${p}\n`;
  out += `author ${author}\ncommitter ${committer}\n\n${message}`;
  return Buffer.from(out, 'utf8');
}

/** {object, type, tag, tagger, message} from raw tag bytes. */
export function parseTag(data) {
  const text = Buffer.isBuffer(data) ? data.toString('utf8') : data;
  const headEnd = text.indexOf('\n\n');
  const head = headEnd < 0 ? text : text.slice(0, headEnd);
  const message = headEnd < 0 ? '' : text.slice(headEnd + 2);
  let object = '';
  let type = '';
  let tag = '';
  let tagger = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('object ')) object = line.slice(7).trim();
    else if (line.startsWith('type ')) type = line.slice(5).trim();
    else if (line.startsWith('tag ')) tag = line.slice(4).trim();
    else if (line.startsWith('tagger ')) tagger = line.slice(7);
  }
  return { object, type, tag, tagger, message };
}

export function buildTag({ object, type, tag, tagger, message }) {
  return Buffer.from(`object ${object}\ntype ${type}\ntag ${tag}\ntagger ${tagger}\n\n${message}`, 'utf8');
}

// ---------------------------------------------------------------- pkt-line

export function encodePktLine(payload) {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const len = body.length + 4;
  const head = Buffer.alloc(4);
  head.write(len.toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([head, body]);
}

export function pktFlush() {
  return Buffer.from('0000', 'ascii');
}

export function pktDelim() {
  return Buffer.from('0001', 'ascii');
}

export function encodePktLines(lines) {
  const parts = [];
  for (const line of lines) {
    if (line === 'flush') parts.push(pktFlush());
    else if (line === 'delim') parts.push(pktDelim());
    else parts.push(encodePktLine(line));
  }
  return Buffer.concat(parts);
}

/** Split a buffer into pkt-line packets: {kind: 'data'|'flush'|'delim'|'response-end', payload}. */
export function decodePktLines(buf) {
  const packets = [];
  let off = 0;
  const b = Buffer.isBuffer(buf) ? buf : Buffer.from(buf);
  while (off < b.length) {
    if (off + 4 > b.length) throw new Error('truncated pkt-line length');
    const hex = b.toString('ascii', off, off + 4);
    const len = parseInt(hex, 16);
    if (Number.isNaN(len)) throw new Error(`bad pkt-line length ${JSON.stringify(hex)}`);
    if (len === 0) {
      packets.push({ kind: 'flush', payload: Buffer.alloc(0) });
      off += 4;
    } else if (len === 1) {
      packets.push({ kind: 'delim', payload: Buffer.alloc(0) });
      off += 4;
    } else if (len === 2) {
      packets.push({ kind: 'response-end', payload: Buffer.alloc(0) });
      off += 4;
    } else {
      if (off + len > b.length) throw new Error('truncated pkt-line payload');
      packets.push({ kind: 'data', payload: b.subarray(off + 4, off + len) });
      off += len;
    }
  }
  return packets;
}

// ---------------------------------------------------------------- packfile

const TYPE_CODE = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPE = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function readVarintSize(buffer, start) {
  let byte = buffer[start];
  const first = byte;
  let size = byte & 0x0f;
  let shift = 4;
  let offset = start + 1;
  while (byte & 0x80) {
    if (offset >= buffer.length) throw new Error('pack entry size varint is truncated');
    byte = buffer[offset++];
    size += (byte & 0x7f) * 2 ** shift;
    shift += 7;
    if (shift > 63) throw new Error('pack entry size varint is too long');
  }
  return { size, next: offset, first };
}

function readOfsDeltaBase(buffer, start) {
  let byte = buffer[start];
  let offset = start + 1;
  let value = byte & 0x7f;
  while (byte & 0x80) {
    if (offset >= buffer.length) throw new Error('ofs-delta base offset is truncated');
    byte = buffer[offset++];
    value = ((value + 1) * 128) + (byte & 0x7f);
  }
  return { baseOffset: value, next: offset };
}

/** Inflate one zlib stream at `offset`; returns its bytes and the offset just past it. */
export function inflateAt(buffer, offset) {
  const view = buffer.subarray(offset);
  let result;
  try {
    result = zlib.inflateSync(view, { info: true });
  } catch (err) {
    throw new Error(`zlib stream at offset ${offset} did not inflate: ${err.message}`);
  }
  const written = result.engine.bytesWritten;
  if (!written || written <= 0) throw new Error(`zlib stream at offset ${offset} consumed no bytes`);
  return { data: result.buffer, next: offset + written };
}

export function applyDelta(base, delta) {
  const baseBuffer = Buffer.isBuffer(base) ? base : Buffer.from(base);
  const deltaBuffer = Buffer.isBuffer(delta) ? delta : Buffer.from(delta);
  let offset = 0;
  const readSize = () => {
    let value = 0;
    let shift = 0;
    for (;;) {
      if (offset >= deltaBuffer.length) throw new Error('delta size varint is truncated');
      const byte = deltaBuffer[offset++];
      value += (byte & 0x7f) * 2 ** shift;
      shift += 7;
      if (!(byte & 0x80)) break;
      if (shift > 63) throw new Error('delta size varint is too long');
    }
    return value;
  };
  const sourceSize = readSize();
  const targetSize = readSize();
  if (sourceSize !== baseBuffer.length) throw new Error(`delta expects a ${sourceSize}-byte base, got ${baseBuffer.length}`);
  const out = Buffer.allocUnsafe(targetSize);
  let written = 0;
  while (offset < deltaBuffer.length) {
    const op = deltaBuffer[offset++];
    if (op & 0x80) {
      let copyOffset = 0;
      let copySize = 0;
      let shift = 0;
      for (let bit = 0; bit < 4; bit += 1) {
        if (op & (1 << bit)) {
          if (offset >= deltaBuffer.length) throw new Error('delta copy offset is truncated');
          copyOffset += deltaBuffer[offset++] * 2 ** shift;
        }
        shift += 8;
      }
      shift = 0;
      for (let bit = 4; bit < 7; bit += 1) {
        if (op & (1 << bit)) {
          if (offset >= deltaBuffer.length) throw new Error('delta copy size is truncated');
          copySize += deltaBuffer[offset++] * 2 ** shift;
        }
        shift += 8;
      }
      if (copySize === 0) copySize = 0x10000;
      if (copyOffset + copySize > baseBuffer.length) throw new Error('delta copy is out of the base');
      if (written + copySize > targetSize) throw new Error('delta writes past its target size');
      baseBuffer.copy(out, written, copyOffset, copyOffset + copySize);
      written += copySize;
    } else if (op !== 0) {
      const literal = op & 0x7f;
      if (offset + literal > deltaBuffer.length) throw new Error('delta insert is truncated');
      if (written + literal > targetSize) throw new Error('delta writes past its target size');
      deltaBuffer.copy(out, written, offset, offset + literal);
      offset += literal;
      written += literal;
    } else {
      throw new Error('delta opcode 0 is invalid');
    }
  }
  if (written !== targetSize) throw new Error(`delta produced ${written} of ${targetSize} bytes`);
  return out;
}

/**
 * Read a packfile and resolve every object (full objects plus OFS_DELTA and
 * REF_DELTA). `resolveBase(oid)` supplies a base object a thin pack leaves out.
 * Returns {objects: Map<oid, {type, data}>, deltaCount, declaredCount, version}.
 */
export function readPack(pack, options = {}) {
  const buffer = Buffer.isBuffer(pack) ? pack : Buffer.from(pack);
  if (buffer.length < 32) throw new Error(`pack is ${buffer.length} bytes, too short`);
  if (buffer.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('pack does not start with PACK');
  const version = buffer.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`unsupported pack version ${version}`);
  const declaredCount = buffer.readUInt32BE(8);
  const trailerStart = buffer.length - 20;
  const trailer = buffer.subarray(trailerStart).toString('hex');
  const computedTrailer = sha1Hex(buffer.subarray(0, trailerStart));
  if (trailer !== computedTrailer) throw new Error('pack trailer checksum mismatch');
  const objects = new Map();
  const byOffset = new Map(); // pack offset -> oid
  let offset = 12;
  let deltaCount = 0;
  // First pass: read raw entries.
  const raw = [];
  for (let i = 0; i < declaredCount; i += 1) {
    const entryOffset = offset;
    const { size, next, first } = readVarintSize(buffer, offset);
    const typeCode = (first >> 4) & 0x7;
    offset = next;
    if (typeCode === 6) {
      // OFS_DELTA
      const { baseOffset, next: afterBase } = readOfsDeltaBase(buffer, offset);
      offset = afterBase;
      const { data, next: afterData } = inflateAt(buffer, offset);
      offset = afterData;
      raw.push({ kind: 'ofs-delta', baseOffset: entryOffset - baseOffset, delta: data, size, offset: entryOffset });
      deltaCount += 1;
    } else if (typeCode === 7) {
      // REF_DELTA
      const baseOid = buffer.subarray(offset, offset + 20).toString('hex');
      offset += 20;
      const { data, next: afterData } = inflateAt(buffer, offset);
      offset = afterData;
      raw.push({ kind: 'ref-delta', baseOid, delta: data, size, offset: entryOffset });
      deltaCount += 1;
    } else {
      const type = CODE_TYPE[typeCode];
      if (!type) throw new Error(`unknown pack object type ${typeCode}`);
      const { data, next: afterData } = inflateAt(buffer, offset);
      offset = afterData;
      if (data.length !== size) throw new Error(`pack object size mismatch: declared ${size}, got ${data.length}`);
      const oid = hashObject(type, data);
      objects.set(oid, { type, data });
      byOffset.set(entryOffset, oid);
    }
  }
  if (offset !== trailerStart) throw new Error(`pack entries end at ${offset}, trailer at ${trailerStart}`);
  // Second pass: resolve deltas (may chain; iterate until stable).
  const pending = raw.filter((e) => e.kind === 'ofs-delta' || e.kind === 'ref-delta');
  const resolveBase = options.resolveBase;
  let guard = pending.length + 2;
  while (pending.length > 0) {
    if (guard-- <= 0) throw new Error('delta chain did not resolve');
    let progressed = false;
    for (let i = pending.length - 1; i >= 0; i -= 1) {
      const entry = pending[i];
      let base = null;
      if (entry.kind === 'ofs-delta') {
        const baseOid = byOffset.get(entry.baseOffset);
        if (baseOid) base = objects.get(baseOid);
      } else {
        base = objects.get(entry.baseOid) ?? (resolveBase ? resolveBase(entry.baseOid) : undefined);
      }
      if (!base) continue;
      const data = applyDelta(base.data, entry.delta);
      // The delta result's type is its base's type.
      const oid = hashObject(base.type, data);
      if (!objects.has(oid)) objects.set(oid, { type: base.type, data });
      byOffset.set(entry.offset, oid);
      pending.splice(i, 1);
      progressed = true;
    }
    if (!progressed) throw new Error('delta base object is missing from the pack');
  }
  return { objects, deltaCount, declaredCount, version };
}

function writePackObjectHeader(type, size) {
  const code = TYPE_CODE[type];
  const bytes = [];
  let first = (code << 4) | (size & 0x0f);
  size >>= 4;
  if (size > 0) first |= 0x80;
  bytes.push(first);
  while (size > 0) {
    let b = size & 0x7f;
    size >>= 7;
    if (size > 0) b |= 0x80;
    bytes.push(b);
  }
  return Buffer.from(bytes);
}

/** Build a packfile (version 2, no deltas) from [{type, data}]. */
export function writePack(objects) {
  const list = [...objects];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(list.length, 8);
  const parts = [header];
  for (const obj of list) {
    const data = Buffer.isBuffer(obj.data) ? obj.data : Buffer.from(obj.data);
    parts.push(writePackObjectHeader(obj.type, data.length));
    parts.push(zlib.deflateSync(data));
  }
  const body = Buffer.concat(parts);
  const trailer = Buffer.from(sha1Hex(body), 'hex');
  return Buffer.concat([body, trailer]);
}

/** All oids reachable from `roots` through commits, trees and tags (lookup: oid -> {type, data}). */
export function collectReachable(roots, lookup) {
  const seen = new Set();
  const stack = [...roots];
  while (stack.length > 0) {
    const oid = stack.pop();
    if (!oid || oid === ZERO_OID || seen.has(oid)) continue;
    const obj = lookup(oid);
    if (!obj) continue;
    seen.add(oid);
    if (obj.type === 'commit') {
      const c = parseCommit(obj.data);
      stack.push(c.tree);
      for (const p of c.parents) stack.push(p);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) stack.push(e.oid);
    } else if (obj.type === 'tag') {
      stack.push(parseTag(obj.data).object);
    }
  }
  return seen;
}

/** Is `ancestor` an ancestor of (or equal to) `oid`? Walks commit parents only. */
export function isAncestor(ancestor, oid, lookup) {
  if (ancestor === oid) return true;
  if (!ancestor || ancestor === ZERO_OID || !oid || oid === ZERO_OID) return false;
  const seen = new Set();
  const stack = [oid];
  while (stack.length > 0) {
    const cur = stack.pop();
    if (seen.has(cur)) continue;
    seen.add(cur);
    const obj = lookup(cur);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) {
      if (p === ancestor) return true;
      stack.push(p);
    }
  }
  return false;
}
