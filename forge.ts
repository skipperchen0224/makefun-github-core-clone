// forge.ts — the forge itself: in-memory store, REST v3, GraphQL v4, MCP and git smart HTTP.
// Plain JavaScript in a .ts file so Node 22's type stripping runs it as-is.
// Deterministic by design: timestamps come from a fixed epoch plus a counter, never the clock.

import { createServer } from 'node:http';
import {
  ZERO_OID, isOid, hashObject, parseTree, buildTree, parseCommit, buildCommit,
  parseTag, buildTag, encodePktLine, encodePktLines, pktFlush, decodePktLines,
  readPack, writePack, collectReachable, isAncestor,
} from './git.ts';

// ---------------------------------------------------------------- scenario identity
// The suite's data is deterministic from one public seed (wire.ts SCENARIO_SEED).
// The bearer token names the scenario's viewer; re-derive that login here so a
// repository under any other owner is a 404 for this token, as the suite expects.

const U64_MASK = 0xffffffffffffffffn;
function fnv1a64(text) {
  let hash = 0xcbf29ce484222325n;
  for (let i = 0; i < text.length; i += 1) {
    hash ^= BigInt(text.charCodeAt(i));
    hash = (hash * 0x100000001b3n) & U64_MASK;
  }
  return hash;
}
function mix64(value) {
  let z = (value + 0x9e3779b97f4a7c15n) & U64_MASK;
  z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & U64_MASK;
  z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & U64_MASK;
  return (z ^ (z >> 31n)) & U64_MASK;
}
const SCENARIO_SEED = 0x6a09e667f3bcc909n;
class Rng {
  constructor(seed) {
    const masked = seed & U64_MASK;
    this.state = masked === 0n ? SCENARIO_SEED : masked;
  }
  nextU64() {
    let x = this.state;
    x = (x ^ (x >> 12n)) & U64_MASK;
    x = (x ^ (x << 25n)) & U64_MASK;
    x = (x ^ (x >> 27n)) & U64_MASK;
    this.state = x;
    return (x * 0x2545f4914f6cdd1dn) & U64_MASK;
  }
  nextU32() { return Number(this.nextU64() >> 32n); }
  nextInt(max) {
    if (max === 1) return 0;
    const range = 4294967296;
    const limit = range - (range % max);
    for (;;) {
      const v = this.nextU32();
      if (v < limit) return v % max;
    }
  }
  pick(items) { return items[this.nextInt(items.length)]; }
}
function scenarioRng(label) {
  return new Rng(mix64(SCENARIO_SEED ^ fnv1a64(label)));
}
const FIRST_NAMES = ['ada', 'bram', 'cora', 'dmitri', 'elena', 'felix', 'greta', 'hugo', 'iris', 'jonas', 'kira', 'lars', 'mira', 'nico', 'olga', 'pavel', 'quinn', 'rosa', 'sven', 'tess', 'ulla', 'vito', 'wren', 'yara', 'zane'];
const LAST_NAMES = ['anders', 'bauer', 'costa', 'dahl', 'eriksen', 'fischer', 'garcia', 'holm', 'iversen', 'jansen', 'keller', 'lind', 'moreau', 'novak', 'olsen', 'peters', 'quist', 'rossi', 'sato', 'turi', 'ulrich', 'vega', 'weber', 'xu', 'yilmaz', 'zimmer'];
function deriveViewer() {
  const rng = scenarioRng('users');
  const used = new Set();
  const users = [];
  for (let i = 0; i < 12; i += 1) {
    const first = rng.pick(FIRST_NAMES);
    const last = rng.pick(LAST_NAMES);
    const base = `${first}${last}`.replace(/[^a-z0-9-]/g, '');
    let login = base;
    let suffix = 2;
    while (used.has(login)) { login = `${base}-${suffix}`; suffix += 1; }
    used.add(login);
    users.push({ id: 1000 + i, login, name: `${first} ${last}`, email: `${login}@example.invalid` });
  }
  return { viewer: users[0], stranger: users[2] };
}
const { viewer: VIEWER, stranger: STRANGER } = deriveViewer();

// ---------------------------------------------------------------- deterministic clock
const EPOCH_SEC = 1735689600; // 2025-01-01T00:00:00Z
let tick = 0;
function nextIso() {
  tick += 1;
  return new Date((EPOCH_SEC + tick) * 1000).toISOString();
}
function nextStamp() {
  tick += 1;
  return EPOCH_SEC + tick;
}

// ---------------------------------------------------------------- store

let repoIdSeq = 5000;
let commentIdSeq = 1;
let globalIdSeq = 1;
/** key `${owner}/${name}` -> repo */
const repos = new Map();

function gid(kind, payload) {
  return Buffer.from(`${kind}:${payload}`, 'utf8').toString('base64url');
}
function decodeGid(id) {
  try {
    const text = Buffer.from(String(id), 'base64url').toString('utf8');
    const colon = text.indexOf(':');
    if (colon < 0) return null;
    return { kind: text.slice(0, colon), payload: text.slice(colon + 1) };
  } catch {
    return null;
  }
}

function newRepo(owner, name, opts = {}) {
  const now = nextIso();
  return {
    id: repoIdSeq++,
    name,
    owner,
    description: opts.description ?? '',
    private: opts.private ?? false,
    defaultBranch: 'main',
    createdSeq: tick,
    createdAt: now,
    updatedAt: now,
    objects: new Map(), // oid -> {type, data}
    refs: new Map(), // refname -> oid
    issues: new Map(), // number -> issue
    pulls: new Map(), // number -> pull
    nextNumber: 1,
    labels: new Map(), // name -> {name, color, description}
    comments: new Map(), // issue number -> [comment]
  };
}

function repoKey(owner, name) { return `${owner}/${name}`; }
function getRepo(owner, name) { return repos.get(repoKey(owner, name)) ?? null; }
function putObject(repo, type, data) {
  const buf = Buffer.isBuffer(data) ? data : Buffer.from(data);
  const oid = hashObject(type, buf);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data: buf });
  return oid;
}
function lookup(repo, oid) { return repo.objects.get(oid) ?? null; }

/** Flatten a commit's tree into path -> {oid, mode}. */
function flattenTree(repo, treeOid, prefix = '', out = new Map()) {
  const obj = lookup(repo, treeOid);
  if (!obj || obj.type !== 'tree') return out;
  for (const e of parseTree(obj.data)) {
    const path = prefix === '' ? e.name : `${prefix}/${e.name}`;
    if (e.mode === '40000') flattenTree(repo, e.oid, path, out);
    else out.set(path, { oid: e.oid, mode: e.mode });
  }
  return out;
}

/** Build (and store) nested tree objects from a flat path map; returns the root tree oid. */
function buildTreeFromMap(repo, flat) {
  const build = (prefix) => {
    const entries = [];
    const dirs = new Map();
    for (const [path, entry] of flat) {
      if (!path.startsWith(prefix)) continue;
      const rest = path.slice(prefix.length);
      const slash = rest.indexOf('/');
      if (slash < 0) entries.push({ mode: entry.mode, name: rest, oid: entry.oid });
      else {
        const dir = rest.slice(0, slash);
        if (!dirs.has(dir)) dirs.set(dir, true);
      }
    }
    for (const dir of dirs.keys()) {
      entries.push({ mode: '40000', name: dir, oid: build(prefix === '' ? `${dir}/` : `${prefix}${dir}/`) });
    }
    return putObject(repo, 'tree', buildTree(entries));
  };
  return build('');
}

/** Commit `files` (flat path map, full new tree state) onto `branch`; returns the commit oid. */
function commitTree(repo, branch, flat, message) {
  const treeOid = buildTreeFromMap(repo, flat);
  const tip = repo.refs.get(`refs/heads/${branch}`) ?? null;
  const stamp = nextStamp();
  const ident = `${VIEWER.name} <${VIEWER.email}> ${stamp} +0000`;
  const commit = buildCommit({
    tree: treeOid,
    parents: tip ? [tip] : [],
    author: ident,
    committer: ident,
    message: message.endsWith('\n') ? message : `${message}\n`,
  });
  const oid = putObject(repo, 'commit', commit);
  repo.refs.set(`refs/heads/${branch}`, oid);
  repo.updatedAt = nextIso();
  return oid;
}

/** Commits reachable from `tip`, newest first (BFS from the tip). */
function listCommits(repo, tip, limit = 100) {
  const out = [];
  const seen = new Set();
  const queue = [tip];
  while (queue.length > 0 && out.length < limit) {
    const oid = queue.shift();
    if (!oid || oid === ZERO_OID || seen.has(oid)) continue;
    seen.add(oid);
    const obj = lookup(repo, oid);
    if (!obj || obj.type !== 'commit') continue;
    out.push(oid);
    for (const p of parseCommit(obj.data).parents) queue.push(p);
  }
  return out;
}

/** Best common ancestor of two commits (first found walking from `a`). */
function mergeBase(repo, a, b) {
  if (!a || !b) return null;
  const ancestorsB = new Set();
  const stackB = [b];
  while (stackB.length > 0) {
    const cur = stackB.pop();
    if (!cur || cur === ZERO_OID || ancestorsB.has(cur)) continue;
    ancestorsB.add(cur);
    const obj = lookup(repo, cur);
    if (obj && obj.type === 'commit') for (const p of parseCommit(obj.data).parents) stackB.push(p);
  }
  const stackA = [a];
  const seen = new Set();
  while (stackA.length > 0) {
    const cur = stackA.shift();
    if (!cur || cur === ZERO_OID || seen.has(cur)) continue;
    seen.add(cur);
    if (ancestorsB.has(cur)) return cur;
    const obj = lookup(repo, cur);
    if (obj && obj.type === 'commit') for (const p of parseCommit(obj.data).parents) stackA.push(p);
  }
  return null;
}

/** Diff two flat trees: [{filename, status, additions, deletions, changes}]. */
function diffTrees(oldFlat, newFlat) {
  const files = [];
  const paths = new Set([...oldFlat.keys(), ...newFlat.keys()]);
  for (const path of [...paths].sort()) {
    const oldE = oldFlat.get(path);
    const newE = newFlat.get(path);
    if (oldE && !newE) {
      const oldText = '';
      void oldText;
      files.push({ filename: path, status: 'removed', additions: 0, deletions: 1, changes: 1 });
    } else if (!oldE && newE) {
      files.push({ filename: path, status: 'added', additions: 1, deletions: 0, changes: 1 });
    } else if (oldE.oid !== newE.oid) {
      files.push({ filename: path, status: 'modified', additions: 1, deletions: 1, changes: 2 });
    }
  }
  return files;
}

/** Count lines of a blob's text (for additions/deletions). */
function lineCount(repo, oid) {
  const obj = lookup(repo, oid);
  if (!obj) return 0;
  const text = obj.data.toString('utf8');
  if (text === '') return 0;
  return text.split('\n').length - (text.endsWith('\n') ? 1 : 0);
}

/** Diff with real line counts (used for pull files). */
function diffTreesCounted(repo, oldFlat, newFlat) {
  const files = [];
  const paths = new Set([...oldFlat.keys(), ...newFlat.keys()]);
  for (const path of [...paths].sort()) {
    const oldE = oldFlat.get(path);
    const newE = newFlat.get(path);
    if (oldE && !newE) {
      const del = lineCount(repo, oldE.oid);
      files.push({ filename: path, status: 'removed', additions: 0, deletions: Math.max(del, 1), changes: Math.max(del, 1) });
    } else if (!oldE && newE) {
      const add = lineCount(repo, newE.oid);
      files.push({ filename: path, status: 'added', additions: Math.max(add, 1), deletions: 0, changes: Math.max(add, 1) });
    } else if (oldE.oid !== newE.oid) {
      const oldLines = new Set(lookup(repo, oldE.oid)?.data.toString('utf8').split('\n') ?? []);
      const newLines = new Set(lookup(repo, newE.oid)?.data.toString('utf8').split('\n') ?? []);
      let additions = 0;
      for (const l of newLines) if (!oldLines.has(l)) additions += 1;
      let deletions = 0;
      for (const l of oldLines) if (!newLines.has(l)) deletions += 1;
      if (additions === 0 && deletions === 0) { additions = 1; deletions = 1; }
      files.push({ filename: path, status: 'modified', additions, deletions, changes: additions + deletions });
    }
  }
  return files;
}

// ---------------------------------------------------------------- HTTP plumbing

const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
let requestSeq = 0;

function sendJson(res, status, body, extraHeaders = {}) {
  const text = `${JSON.stringify(body)}\n`;
  requestSeq += 1;
  res.writeHead(status, {
    'content-type': 'application/json; charset=utf-8',
    'content-length': Buffer.byteLength(text),
    'x-github-request-id': `req-${requestSeq}`,
    ...extraHeaders,
  });
  res.end(text);
}

function sendBytes(res, status, body, contentType, extraHeaders = {}) {
  requestSeq += 1;
  res.writeHead(status, {
    'content-type': contentType,
    'content-length': body.length,
    'x-github-request-id': `req-${requestSeq}`,
    ...extraHeaders,
  });
  res.end(body);
}

function errJson(res, status, message) {
  sendJson(res, status, { message });
}

function readBody(req) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    req.on('data', (c) => chunks.push(c));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function authed(req) {
  if (TOKEN === '') return true;
  const header = req.headers.authorization ?? '';
  return header === `Bearer ${TOKEN}`;
}

function pathOf(req) {
  try {
    return new URL(req.url ?? '/', 'http://entry').pathname;
  } catch {
    return '/';
  }
}

function queryOf(req) {
  try {
    return new URL(req.url ?? '/', 'http://entry').searchParams;
  } catch {
    return new URLSearchParams();
  }
}

function decodeSegment(s) {
  try { return decodeURIComponent(s); } catch { return s; }
}

/** Parse a JSON body; returns {ok, value} or sends 400 and returns {ok:false}. */
async function jsonBody(req, res) {
  const raw = await readBody(req);
  if (raw.length === 0) return { ok: true, value: {} };
  try {
    return { ok: true, value: JSON.parse(raw.toString('utf8')) };
  } catch {
    errJson(res, 400, 'Problems parsing JSON');
    return { ok: false, value: null };
  }
}

function parsePagination(query) {
  const perPageRaw = Number.parseInt(query.get('per_page') ?? '30', 10);
  const pageRaw = Number.parseInt(query.get('page') ?? '1', 10);
  const perPage = Number.isFinite(perPageRaw) ? Math.min(Math.max(perPageRaw, 1), 100) : 30;
  const page = Number.isFinite(pageRaw) ? Math.max(pageRaw, 1) : 1;
  return { perPage, page };
}

/** Paginate `items`; returns {page, link} where link is a Link header value or ''. */
function paginate(req, items, query) {
  const { perPage, page } = parsePagination(query);
  const total = items.length;
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  let link = '';
  if (start + perPage < total) {
    const base = `${req.headers.host ? `http://${req.headers.host}` : ''}${pathOf(req)}`;
    const next = new URL(base);
    next.searchParams.set('per_page', String(perPage));
    next.searchParams.set('page', String(page + 1));
    link = `<${next.toString()}>; rel="next"`;
  }
  return { page: slice, link };
}

// ---------------------------------------------------------------- REST serializers

function repoJson(repo) {
  return {
    id: repo.id,
    node_id: gid('R', `${repo.owner}/${repo.name}`),
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: VIEWER.id, type: 'User' },
    private: repo.private,
    description: repo.description,
    default_branch: repo.defaultBranch,
    created_at: repo.createdAt,
    updated_at: repo.updatedAt,
    pushed_at: repo.updatedAt,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    clone_url: `https://example.invalid/${repo.owner}/${repo.name}.git`,
    git_url: `git://example.invalid/${repo.owner}/${repo.name}.git`,
    ssh_url: `git@example.invalid:${repo.owner}/${repo.name}.git`,
    homepage: null,
    language: null,
    fork: false,
    forks_count: 0,
    stargazers_count: 0,
    watchers_count: 0,
    open_issues_count: [...repo.issues.values()].filter((i) => i.state === 'open').length,
    has_issues: true,
    has_projects: false,
    has_wiki: false,
    archived: false,
    disabled: false,
    visibility: repo.private ? 'private' : 'public',
  };
}

function issueJson(repo, issue) {
  return {
    id: issue.id,
    node_id: issue.nodeId,
    number: issue.number,
    title: issue.title,
    body: issue.body ?? '',
    state: issue.state,
    labels: issue.labels.map((name) => {
      const label = repo.labels.get(name);
      return { id: globalIdSeq, name, color: label?.color ?? 'ededed', description: label?.description ?? '' };
    }),
    user: { login: VIEWER.login, id: VIEWER.id, type: 'User' },
    assignee: null,
    assignees: [],
    created_at: issue.createdAt,
    updated_at: issue.updatedAt,
    closed_at: issue.closedAt,
    comments: (repo.comments.get(issue.number) ?? []).length,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}/issues/${issue.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}`,
  };
}

function pullJson(repo, pull) {
  return {
    id: pull.id,
    node_id: pull.nodeId,
    number: pull.number,
    title: pull.title,
    body: pull.body ?? '',
    state: pull.state,
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    mergeable: pull.mergeable,
    head: { ref: pull.head.ref, sha: pull.head.sha, label: `${repo.owner}:${pull.head.ref}` },
    base: { ref: pull.base.ref, sha: pull.base.sha, label: `${repo.owner}:${pull.base.ref}` },
    user: { login: VIEWER.login, id: VIEWER.id, type: 'User' },
    created_at: pull.createdAt,
    updated_at: pull.updatedAt,
    closed_at: pull.closedAt,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}/pull/${pull.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pull.number}`,
  };
}

function createIssueInRepo(repo, { title, body, labels }) {
  const number = repo.nextNumber++;
  const now = nextIso();
  const issue = {
    id: repo.id * 100000 + number,
    nodeId: gid('I', `${repo.owner}/${repo.name}#${number}`),
    number,
    title,
    body: body ?? '',
    state: 'open',
    labels: [...(labels ?? [])],
    createdSeq: tick,
    createdAt: now,
    updatedAt: now,
    closedAt: null,
  };
  repo.issues.set(number, issue);
  return issue;
}

function createPullInRepo(repo, { title, body, head, base }) {
  const headSha = repo.refs.get(`refs/heads/${head}`) ?? null;
  const baseSha = repo.refs.get(`refs/heads/${base}`) ?? null;
  const number = repo.nextNumber++;
  const now = nextIso();
  const baseTree = baseSha ? flattenTree(repo, parseCommit(lookup(repo, baseSha).data).tree) : new Map();
  const headTree = headSha ? flattenTree(repo, parseCommit(lookup(repo, headSha).data).tree) : new Map();
  const files = diffTreesCounted(repo, baseTree, headTree);
  const pull = {
    id: repo.id * 100000 + number,
    nodeId: gid('P', `${repo.owner}/${repo.name}#${number}`),
    number,
    title,
    body: body ?? '',
    state: 'open',
    merged: false,
    mergedAt: null,
    mergeCommitSha: null,
    mergeable: true,
    head: { ref: head, sha: headSha },
    base: { ref: base, sha: baseSha },
    files,
    createdSeq: tick,
    createdAt: now,
    updatedAt: now,
    closedAt: null,
  };
  repo.pulls.set(number, pull);
  return pull;
}

/** Does merging `pull` conflict? (three-way: base tip vs merge-base vs head). */
function pullConflict(repo, pull) {
  const headSha = pull.head.sha;
  const baseSha = repo.refs.get(`refs/heads/${pull.base.ref}`) ?? pull.base.sha;
  if (!headSha || !baseSha) return false;
  const base = mergeBase(repo, headSha, baseSha);
  if (!base) return false;
  const baseTree = flattenTree(repo, parseCommit(lookup(repo, base).data).tree);
  const headTree = flattenTree(repo, parseCommit(lookup(repo, headSha).data).tree);
  const tipTree = flattenTree(repo, parseCommit(lookup(repo, baseSha).data).tree);
  for (const [path, headE] of headTree) {
    const baseE = baseTree.get(path);
    const tipE = tipTree.get(path);
    const headChanged = !baseE || baseE.oid !== headE.oid;
    const tipChanged = (baseE?.oid ?? null) !== (tipE?.oid ?? null);
    if (headChanged && tipChanged && (tipE?.oid ?? null) !== headE.oid) return true;
  }
  for (const [path, baseE] of baseTree) {
    if (!headTree.has(path)) {
      const tipE = tipTree.get(path);
      if ((tipE?.oid ?? null) !== baseE.oid) return true;
    }
  }
  return false;
}

/** Squash-merge `pull` onto its base branch. Returns the merge commit oid or null on conflict. */
function mergePull(repo, pull) {
  if (pullConflict(repo, pull)) return null;
  const headSha = pull.head.sha;
  const baseSha = repo.refs.get(`refs/heads/${pull.base.ref}`) ?? pull.base.sha;
  const base = mergeBase(repo, headSha, baseSha);
  const baseTree = base ? flattenTree(repo, parseCommit(lookup(repo, base).data).tree) : new Map();
  const headTree = flattenTree(repo, parseCommit(lookup(repo, headSha).data).tree);
  const tipTree = flattenTree(repo, parseCommit(lookup(repo, baseSha).data).tree);
  // Three-way result: start from the base tip's tree, apply head's changes vs merge-base.
  const result = new Map(tipTree);
  for (const [path, headE] of headTree) {
    const baseE = baseTree.get(path);
    if (!baseE || baseE.oid !== headE.oid) result.set(path, headE);
  }
  for (const [path, baseE] of baseTree) {
    if (!headTree.has(path) && result.get(path)?.oid === baseE.oid) result.delete(path);
  }
  const treeOid = buildTreeFromMap(repo, result);
  const stamp = nextStamp();
  const ident = `${VIEWER.name} <${VIEWER.email}> ${stamp} +0000`;
  const message = `Merge pull request #${pull.number} from ${repo.owner}/${pull.head.ref}\n\n${pull.title}\n`;
  const commit = buildCommit({ tree: treeOid, parents: [baseSha], author: ident, committer: ident, message });
  const oid = putObject(repo, 'commit', commit);
  repo.refs.set(`refs/heads/${pull.base.ref}`, oid);
  repo.updatedAt = nextIso();
  pull.state = 'closed';
  pull.merged = true;
  pull.mergedAt = nextIso();
  pull.mergeCommitSha = oid;
  pull.closedAt = pull.mergedAt;
  pull.updatedAt = pull.mergedAt;
  return oid;
}

// ---------------------------------------------------------------- REST v3

function repoFromPath(owner, name) {
  if (owner !== VIEWER.login) return null; // another owner's repo is 404, never 403
  return getRepo(owner, name);
}

async function handleRest(req, res, path, method, query) {
  // GET /api/v3/ — the API root.
  if ((path === '/api/v3' || path === '/api/v3/') && method === 'GET') {
    sendJson(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit' }, { 'x-oauth-scopes': 'repo, read:org' });
    return true;
  }
  if (path === '/api/v3/meta' && method === 'GET') {
    sendJson(res, 200, { installed_version: '1.0.0' });
    return true;
  }
  if (path === '/api/v3/user' && method === 'GET') {
    sendJson(res, 200, { login: VIEWER.login, id: VIEWER.id, name: VIEWER.name, email: VIEWER.email, type: 'User' });
    return true;
  }
  if (path === '/api/v3/user/repos' && method === 'POST') {
    const parsed = await jsonBody(req, res);
    if (!parsed.ok) return true;
    const body = parsed.value ?? {};
    const name = typeof body.name === 'string' ? body.name : '';
    if (name === '') { errJson(res, 422, 'name is required'); return true; }
    if (getRepo(VIEWER.login, name)) { errJson(res, 422, 'Repository already exists'); return true; }
    const repo = newRepo(VIEWER.login, name, { description: body.description ?? '', private: body.private ?? false });
    repos.set(repoKey(repo.owner, repo.name), repo);
    sendJson(res, 201, repoJson(repo));
    return true;
  }
  if (path === '/api/v3/user/repos' && method === 'GET') {
    const all = [...repos.values()].filter((r) => r.owner === VIEWER.login).sort((a, b) => a.createdSeq - b.createdSeq).map(repoJson);
    const { page, link } = paginate(req, all, query);
    sendJson(res, 200, page, link === '' ? {} : { link });
    return true;
  }

  const m = /^\/api\/v3\/repos\/([^/]+)\/([^/]+)(.*)$/.exec(path);
  if (!m) return false;
  const owner = decodeSegment(m[1]);
  const name = decodeSegment(m[2]);
  const rest = m[3] || '';
  const repo = repoFromPath(owner, name);
  if (!repo) { errJson(res, 404, 'Not Found'); return true; }

  // GET /repos/{o}/{r}
  if (rest === '' && method === 'GET') { sendJson(res, 200, repoJson(repo)); return true; }
  // PATCH /repos/{o}/{r}
  if (rest === '' && method === 'PATCH') {
    const parsed = await jsonBody(req, res);
    if (!parsed.ok) return true;
    const body = parsed.value ?? {};
    if (typeof body.description === 'string') repo.description = body.description;
    if (typeof body.private === 'boolean') repo.private = body.private;
    repo.updatedAt = nextIso();
    sendJson(res, 200, repoJson(repo));
    return true;
  }
  // DELETE /repos/{o}/{r}
  if (rest === '' && method === 'DELETE') {
    repos.delete(repoKey(owner, name));
    res.writeHead(204, { 'x-github-request-id': `req-${++requestSeq}` });
    res.end();
    return true;
  }
  // GET /repos/{o}/{r}/branches
  if (rest === '/branches' && method === 'GET') {
    const list = [...repo.refs.entries()]
      .filter(([ref]) => ref.startsWith('refs/heads/'))
      .map(([ref, sha]) => ({ name: ref.slice('refs/heads/'.length), commit: { sha }, protected: false }));
    sendJson(res, 200, list);
    return true;
  }
  // GET /repos/{o}/{r}/branches/{branch}
  const branchMatch = /^\/branches\/(.+)$/.exec(rest);
  if (branchMatch && method === 'GET') {
    const branch = decodeSegment(branchMatch[1]);
    const sha = repo.refs.get(`refs/heads/${branch}`);
    if (!sha) { errJson(res, 404, 'Not Found'); return true; }
    sendJson(res, 200, { name: branch, commit: { sha }, protected: false });
    return true;
  }
  // POST /repos/{o}/{r}/git/refs
  if (rest === '/git/refs' && method === 'POST') {
    const parsed = await jsonBody(req, res);
    if (!parsed.ok) return true;
    const body = parsed.value ?? {};
    const ref = typeof body.ref === 'string' ? body.ref : '';
    const sha = typeof body.sha === 'string' ? body.sha : '';
    if (!ref.startsWith('refs/') || !isOid(sha)) { errJson(res, 422, 'Invalid ref or sha'); return true; }
    if (repo.refs.has(ref)) { errJson(res, 422, 'Reference already exists'); return true; }
    if (!lookup(repo, sha)) { errJson(res, 422, 'Object does not exist'); return true; }
    repo.refs.set(ref, sha);
    sendJson(res, 201, { ref, object: { sha, type: 'commit' } });
    return true;
  }
  // GET /repos/{o}/{r}/git/refs/heads/{branch}
  const refMatch = /^\/git\/refs\/(.+)$/.exec(rest);
  if (refMatch && method === 'GET') {
    const ref = decodeSegment(refMatch[1]);
    const sha = repo.refs.get(ref);
    if (!sha) { errJson(res, 404, 'Not Found'); return true; }
    sendJson(res, 200, { ref, object: { sha, type: 'commit' } });
    return true;
  }
  // GET /repos/{o}/{r}/commits
  if (rest === '/commits' && method === 'GET') {
    const shaParam = query.get('sha');
    const ref = shaParam ? `refs/heads/${shaParam}` : `refs/heads/${repo.defaultBranch}`;
    const tip = repo.refs.get(ref) ?? (shaParam && isOid(shaParam) ? shaParam : null);
    const oids = tip ? listCommits(repo, tip) : [];
    const list = oids.map((oid) => {
      const c = parseCommit(lookup(repo, oid).data);
      return { sha: oid, commit: { message: c.message.replace(/\n+$/, ''), author: { name: VIEWER.name, email: VIEWER.email }, committer: { name: VIEWER.name, email: VIEWER.email } }, parents: c.parents.map((p) => ({ sha: p })) };
    });
    sendJson(res, 200, list);
    return true;
  }
  // Contents: PUT/GET/DELETE /repos/{o}/{r}/contents/{path...}
  const contentsMatch = /^\/contents\/(.*)$/.exec(rest);
  if (contentsMatch) {
    const filePath = contentsMatch[1].split('/').map(decodeSegment).join('/');
    if (method === 'PUT') return handleContentsPut(req, res, repo, filePath);
    if (method === 'GET') return handleContentsGet(req, res, repo, filePath, query);
    if (method === 'DELETE') return handleContentsDelete(req, res, repo, filePath);
    return false;
  }
  // Labels
  if (rest === '/labels' && method === 'POST') {
    const parsed = await jsonBody(req, res);
    if (!parsed.ok) return true;
    const body = parsed.value ?? {};
    const labelName = typeof body.name === 'string' ? body.name : '';
    if (labelName === '') { errJson(res, 422, 'name is required'); return true; }
    const label = { name: labelName, color: typeof body.color === 'string' ? body.color : 'ededed', description: typeof body.description === 'string' ? body.description : '' };
    repo.labels.set(labelName, label);
    sendJson(res, 201, label);
    return true;
  }
  if (rest === '/labels' && method === 'GET') {
    sendJson(res, 200, [...repo.labels.values()]);
    return true;
  }
  // Issues
  if (rest === '/issues' && method === 'POST') {
    const parsed = await jsonBody(req, res);
    if (!parsed.ok) return true;
    const body = parsed.value ?? {};
    const labels = Array.isArray(body.labels) ? body.labels.map((l) => (typeof l === 'string' ? l : l?.name)).filter(Boolean) : [];
    for (const label of labels) {
      if (!repo.labels.has(label)) { errJson(res, 422, `Label does not exist: ${label}`); return true; }
    }
    const issue = createIssueInRepo(repo, { title: body.title ?? '', body: body.body ?? '', labels });
    sendJson(res, 201, issueJson(repo, issue));
    return true;
  }
  if (rest === '/issues' && method === 'GET') {
    const state = query.get('state') ?? 'open';
    const sort = query.get('sort') ?? 'created';
    const direction = query.get('direction') ?? 'desc';
    let list = [...repo.issues.values()];
    if (state !== 'all') list = list.filter((i) => i.state === state);
    if (sort === 'created') list.sort((a, b) => (direction === 'asc' ? a.createdSeq - b.createdSeq : b.createdSeq - a.createdSeq));
    const { page, link } = paginate(req, list.map((i) => issueJson(repo, i)), query);
    sendJson(res, 200, page, link === '' ? {} : { link });
    return true;
  }
  const issueMatch = /^\/issues\/(\d+)(\/comments)?$/.exec(rest);
  if (issueMatch) {
    const number = Number.parseInt(issueMatch[1], 10);
    const issue = repo.issues.get(number);
    if (!issue) { errJson(res, 404, 'Not Found'); return true; }
    if (issueMatch[2] === '/comments' && method === 'POST') {
      const parsed = await jsonBody(req, res);
      if (!parsed.ok) return true;
      const body = parsed.value ?? {};
      const comment = { id: commentIdSeq++, node_id: gid('C', `${repo.owner}/${repo.name}#${number}:${commentIdSeq}`), body: body.body ?? '', user: { login: VIEWER.login, id: VIEWER.id }, created_at: nextIso(), updated_at: nextIso() };
      if (!repo.comments.has(number)) repo.comments.set(number, []);
      repo.comments.get(number).push(comment);
      sendJson(res, 201, comment);
      return true;
    }
    if (issueMatch[2] === '/comments' && method === 'GET') {
      sendJson(res, 200, repo.comments.get(number) ?? []);
      return true;
    }
    if (!issueMatch[2] && method === 'GET') { sendJson(res, 200, issueJson(repo, issue)); return true; }
    if (!issueMatch[2] && method === 'PATCH') {
      const parsed = await jsonBody(req, res);
      if (!parsed.ok) return true;
      const body = parsed.value ?? {};
      if (typeof body.title === 'string') issue.title = body.title;
      if (typeof body.body === 'string') issue.body = body.body;
      if (body.state === 'open' || body.state === 'closed') {
        issue.state = body.state;
        issue.closedAt = body.state === 'closed' ? nextIso() : null;
      }
      issue.updatedAt = nextIso();
      sendJson(res, 200, issueJson(repo, issue));
      return true;
    }
    return false;
  }
  // Pulls
  if (rest === '/pulls' && method === 'POST') {
    const parsed = await jsonBody(req, res);
    if (!parsed.ok) return true;
    const body = parsed.value ?? {};
    const head = typeof body.head === 'string' ? body.head : '';
    const base = typeof body.base === 'string' ? body.base : repo.defaultBranch;
    if (!repo.refs.has(`refs/heads/${head}`)) { errJson(res, 422, 'Head branch does not exist'); return true; }
    if (!repo.refs.has(`refs/heads/${base}`)) { errJson(res, 422, 'Base branch does not exist'); return true; }
    for (const p of repo.pulls.values()) {
      if (p.state === 'open' && p.head.ref === head && p.base.ref === base) { errJson(res, 422, 'A pull request already exists for this branch'); return true; }
    }
    const pull = createPullInRepo(repo, { title: body.title ?? '', body: body.body ?? '', head, base });
    sendJson(res, 201, pullJson(repo, pull));
    return true;
  }
  if (rest === '/pulls' && method === 'GET') {
    const state = query.get('state') ?? 'open';
    let list = [...repo.pulls.values()];
    if (state !== 'all') list = list.filter((p) => p.state === state);
    list.sort((a, b) => b.createdSeq - a.createdSeq);
    const { page, link } = paginate(req, list.map((p) => pullJson(repo, p)), query);
    sendJson(res, 200, page, link === '' ? {} : { link });
    return true;
  }
  const pullMatch = /^\/pulls\/(\d+)(\/files|\/merge)?$/.exec(rest);
  if (pullMatch) {
    const number = Number.parseInt(pullMatch[1], 10);
    const pull = repo.pulls.get(number);
    if (!pull) { errJson(res, 404, 'Not Found'); return true; }
    if (pullMatch[2] === '/files' && method === 'GET') {
      sendJson(res, 200, pull.files);
      return true;
    }
    if (pullMatch[2] === '/merge' && method === 'PUT') {
      const parsed = await jsonBody(req, res);
      if (!parsed.ok) return true;
      if (pull.state !== 'open') { errJson(res, 405, 'Pull request is not open'); return true; }
      const oid = mergePull(repo, pull);
      if (!oid) { errJson(res, 405, 'Merge conflict'); return true; }
      sendJson(res, 200, { sha: oid, merged: true, message: `Pull Request successfully merged` });
      return true;
    }
    if (!pullMatch[2] && method === 'GET') { sendJson(res, 200, pullJson(repo, pull)); return true; }
    return false;
  }
  return false;
}

async function handleContentsPut(req, res, repo, filePath) {
  const parsed = await jsonBody(req, res);
  if (!parsed.ok) return true;
  const body = parsed.value ?? {};
  const branch = typeof body.branch === 'string' ? body.branch : repo.defaultBranch;
  const contentB64 = typeof body.content === 'string' ? body.content : '';
  let bytes;
  try {
    bytes = Buffer.from(contentB64.replace(/[\r\n\t ]+/g, ''), 'base64');
  } catch {
    errJson(res, 422, 'content is not valid base64');
    return true;
  }
  let tip = repo.refs.get(`refs/heads/${branch}`) ?? null;
  if (!tip && branch !== repo.defaultBranch) {
    // A contents write may create a branch from the default tip (the MCP fallback path).
    const defaultTip = repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? null;
    if (defaultTip) { repo.refs.set(`refs/heads/${branch}`, defaultTip); tip = defaultTip; }
  }
  const flat = tip ? flattenTree(repo, parseCommit(lookup(repo, tip).data).tree) : new Map();
  const existing = flat.get(filePath);
  if (existing && typeof body.sha === 'string' && body.sha !== existing.oid) {
    errJson(res, 409, 'sha does not match the current blob');
    return true;
  }
  const blobOid = putObject(repo, 'blob', bytes);
  flat.set(filePath, { oid: blobOid, mode: '100644' });
  const message = typeof body.message === 'string' ? body.message : `Update ${filePath}`;
  const commitOid = commitTree(repo, branch, flat, message);
  const status = existing ? 200 : 201;
  sendJson(res, status, {
    content: { name: filePath.split('/').pop(), path: filePath, sha: blobOid, size: bytes.length, encoding: 'base64', content: bytes.toString('base64'), type: 'file' },
    commit: { sha: commitOid },
  });
  return true;
}

async function handleContentsGet(req, res, repo, filePath, query) {
  const refParam = query.get('ref');
  let tip = null;
  if (refParam) {
    tip = repo.refs.get(`refs/heads/${refParam}`) ?? (isOid(refParam) ? refParam : null);
  } else {
    tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? null;
  }
  if (!tip) { errJson(res, 404, 'Not Found'); return true; }
  const flat = flattenTree(repo, parseCommit(lookup(repo, tip).data).tree);
  const file = flat.get(filePath);
  if (file) {
    const obj = lookup(repo, file.oid);
    sendJson(res, 200, {
      type: 'file',
      encoding: 'base64',
      size: obj.data.length,
      name: filePath.split('/').pop(),
      path: filePath,
      sha: file.oid,
      content: obj.data.toString('base64'),
    });
    return true;
  }
  // Directory listing: direct children of filePath.
  const prefix = filePath === '' ? '' : `${filePath}/`;
  const entries = new Map();
  for (const [path, entry] of flat) {
    if (!path.startsWith(prefix)) continue;
    const rest = path.slice(prefix.length);
    const slash = rest.indexOf('/');
    if (slash < 0) entries.set(rest, { type: 'file', name: rest, path, sha: entry.oid });
    else entries.set(rest.slice(0, slash), { type: 'dir', name: rest.slice(0, slash), path: `${prefix}${rest.slice(0, slash)}`, sha: entry.oid });
  }
  if (entries.size === 0) { errJson(res, 404, 'Not Found'); return true; }
  sendJson(res, 200, [...entries.values()]);
  return true;
}

async function handleContentsDelete(req, res, repo, filePath) {
  const parsed = await jsonBody(req, res);
  if (!parsed.ok) return true;
  const body = parsed.value ?? {};
  const branch = typeof body.branch === 'string' ? body.branch : repo.defaultBranch;
  const tip = repo.refs.get(`refs/heads/${branch}`) ?? null;
  if (!tip) { errJson(res, 404, 'Not Found'); return true; }
  const flat = flattenTree(repo, parseCommit(lookup(repo, tip).data).tree);
  if (!flat.has(filePath)) { errJson(res, 404, 'Not Found'); return true; }
  flat.delete(filePath);
  const message = typeof body.message === 'string' ? body.message : `Delete ${filePath}`;
  const commitOid = commitTree(repo, branch, flat, message);
  sendJson(res, 200, { commit: { sha: commitOid } });
  return true;
}

// ---------------------------------------------------------------- GraphQL v4
// A small hand-rolled executor for exactly the documents gh and github-mcp-server
// send: queries, mutations, variables, inline fragments, aliases, batching.

const GQL_ISSUE_FIELDS = ['id', 'number', 'title', 'state', 'body', 'url', 'createdAt', 'updatedAt', 'author', 'labels', 'comments', 'closedAt', 'repository'];
const GQL_PR_FIELDS = ['id', 'number', 'title', 'body', 'state', 'merged', 'mergeable', 'headRefName', 'baseRefName', 'headRefOid', 'baseRefOid', 'files', 'url', 'createdAt', 'updatedAt', 'mergedAt', 'mergeCommit', 'author', 'repository'];
const GQL_REPO_FIELDS = ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'url', 'description', 'private', 'createdAt', 'updatedAt'];
const GQL_SEARCH_ENUMS = ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION', 'CODE', 'COMMIT', 'LABEL', 'MILESTONE', 'PROJECT'];

function gqlTokenize(src) {
  const tokens = [];
  let i = 0;
  while (i < src.length) {
    const ch = src[i];
    if (ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch === ',') { i += 1; continue; }
    if (ch === '#') { while (i < src.length && src[i] !== '\n') i += 1; continue; }
    if (ch === '{' || ch === '}' || ch === '(' || ch === ')' || ch === '[' || ch === ']' || ch === ':' || ch === '!' || ch === '=' || ch === '@' || ch === '|' || ch === '&') {
      tokens.push({ kind: 'punct', value: ch }); i += 1; continue;
    }
    if (src.startsWith('...', i)) { tokens.push({ kind: 'punct', value: '...' }); i += 3; continue; }
    if (ch === '$') {
      let j = i + 1;
      while (j < src.length && /[A-Za-z0-9_]/.test(src[j])) j += 1;
      tokens.push({ kind: 'var', value: src.slice(i + 1, j) }); i = j; continue;
    }
    if (ch === '"') {
      let j = i + 1;
      let out = '';
      while (j < src.length && src[j] !== '"') {
        if (src[j] === '\\' && j + 1 < src.length) {
          const esc = src[j + 1];
          if (esc === 'n') out += '\n';
          else if (esc === 't') out += '\t';
          else if (esc === 'r') out += '\r';
          else out += esc;
          j += 2;
        } else { out += src[j]; j += 1; }
      }
      tokens.push({ kind: 'string', value: out }); i = j + 1; continue;
    }
    if (/[0-9-]/.test(ch)) {
      let j = i;
      while (j < src.length && /[0-9.eE+-]/.test(src[j])) j += 1;
      tokens.push({ kind: 'number', value: src.slice(i, j) }); i = j; continue;
    }
    if (/[A-Za-z_]/.test(ch)) {
      let j = i;
      while (j < src.length && /[A-Za-z0-9_]/.test(src[j])) j += 1;
      tokens.push({ kind: 'name', value: src.slice(i, j) }); i = j; continue;
    }
    throw new Error(`GraphQL: unexpected character ${JSON.stringify(ch)}`);
  }
  tokens.push({ kind: 'eof', value: '' });
  return tokens;
}

function gqlParse(src) {
  const tokens = gqlTokenize(src);
  let pos = 0;
  const peek = () => tokens[pos];
  const next = () => tokens[pos++];
  const expectPunct = (v) => {
    const t = next();
    if (t.kind !== 'punct' || t.value !== v) throw new Error(`GraphQL: expected ${JSON.stringify(v)}, got ${JSON.stringify(t.value)}`);
  };
  const parseValue = () => {
    const t = next();
    if (t.kind === 'var') return { kind: 'variable', name: t.value };
    if (t.kind === 'string') return { kind: 'string', value: t.value };
    if (t.kind === 'number') return { kind: 'number', value: Number(t.value) };
    if (t.kind === 'name') {
      if (t.value === 'true') return { kind: 'boolean', value: true };
      if (t.value === 'false') return { kind: 'boolean', value: false };
      if (t.value === 'null') return { kind: 'null' };
      return { kind: 'enum', value: t.value };
    }
    if (t.kind === 'punct' && t.value === '[') {
      const items = [];
      while (!(peek().kind === 'punct' && peek().value === ']')) items.push(parseValue());
      next();
      return { kind: 'list', items };
    }
    if (t.kind === 'punct' && t.value === '{') {
      const fields = [];
      while (!(peek().kind === 'punct' && peek().value === '}')) {
        const nameTok = next();
        expectPunct(':');
        fields.push({ name: nameTok.value, value: parseValue() });
      }
      next();
      return { kind: 'object', fields };
    }
    throw new Error(`GraphQL: unexpected value token ${JSON.stringify(t.value)}`);
  };
  const parseArguments = () => {
    const args = [];
    expectPunct('(');
    while (!(peek().kind === 'punct' && peek().value === ')')) {
      const nameTok = next();
      expectPunct(':');
      args.push({ name: nameTok.value, value: parseValue() });
    }
    next();
    return args;
  };
  const parseType = () => {
    const t = next();
    let type;
    if (t.kind === 'punct' && t.value === '[') {
      const inner = parseType();
      expectPunct(']');
      type = `[${inner}]`;
    } else {
      type = t.value;
    }
    if (peek().kind === 'punct' && peek().value === '!') { next(); type += '!'; }
    return type;
  };
  const parseSelectionSet = () => {
    expectPunct('{');
    const selections = [];
    while (!(peek().kind === 'punct' && peek().value === '}')) {
      selections.push(parseSelection());
    }
    next();
    return selections;
  };
  const parseSelection = () => {
    const t = peek();
    if (t.kind === 'punct' && t.value === '...') {
      next();
      const nt = peek();
      if (nt.kind === 'name' && nt.value === 'on') {
        next();
        const typeName = next().value;
        return { kind: 'inline', typeName, selections: parseSelectionSet() };
      }
      if (nt.kind === 'name') {
        next();
        return { kind: 'spread', name: nt.value };
      }
      throw new Error('GraphQL: bad fragment');
    }
    const first = next();
    let alias = null;
    let name = first.value;
    if (peek().kind === 'punct' && peek().value === ':') {
      next();
      alias = name;
      name = next().value;
    }
    let args = [];
    if (peek().kind === 'punct' && peek().value === '(') args = parseArguments();
    // directives: skip @name[(...)]
    while (peek().kind === 'punct' && peek().value === '@') {
      next(); next();
      if (peek().kind === 'punct' && peek().value === '(') parseArguments();
    }
    let selections = null;
    if (peek().kind === 'punct' && peek().value === '{') selections = parseSelectionSet();
    return { kind: 'field', name, alias: alias ?? name, args, selections };
  };
  const parseVariableDefinitions = () => {
    const defs = [];
    if (peek().kind === 'punct' && peek().value === '(') {
      next();
      while (!(peek().kind === 'punct' && peek().value === ')')) {
        const varTok = next(); // $name
        expectPunct(':');
        const type = parseType();
        let defaultValue = undefined;
        if (peek().kind === 'punct' && peek().value === '=') { next(); defaultValue = parseValue(); }
        defs.push({ name: varTok.value, type, defaultValue });
      }
      next();
    }
    return defs;
  };
  const definitions = [];
  while (peek().kind !== 'eof') {
    const t = peek();
    if (t.kind === 'punct' && t.value === '{') {
      definitions.push({ kind: 'operation', operation: 'query', name: null, varDefs: [], selections: parseSelectionSet() });
      continue;
    }
    if (t.kind === 'name' && (t.value === 'query' || t.value === 'mutation' || t.value === 'subscription')) {
      next();
      let name = null;
      if (peek().kind === 'name') name = next().value;
      const varDefs = parseVariableDefinitions();
      const selections = parseSelectionSet();
      definitions.push({ kind: 'operation', operation: t.value, name, varDefs, selections });
      continue;
    }
    if (t.kind === 'name' && t.value === 'fragment') {
      next();
      const name = next().value;
      const onTok = next(); // 'on'
      void onTok;
      const typeName = next().value;
      const selections = parseSelectionSet();
      definitions.push({ kind: 'fragment', name, typeName, selections });
      continue;
    }
    throw new Error(`GraphQL: unexpected definition token ${JSON.stringify(t.value)}`);
  }
  return definitions;
}

function gqlValue(node, variables) {
  if (!node) return undefined;
  switch (node.kind) {
    case 'variable': return variables[node.name];
    case 'string': case 'number': case 'boolean': return node.value;
    case 'null': return null;
    case 'enum': return node.value;
    case 'list': return node.items.map((item) => gqlValue(item, variables));
    case 'object': {
      const out = {};
      for (const f of node.fields) out[f.name] = gqlValue(f.value, variables);
      return out;
    }
    default: return undefined;
  }
}

function gqlArgs(field, variables) {
  const out = {};
  for (const a of field.args) out[a.name] = gqlValue(a.value, variables);
  return out;
}

// Field resolvers: (parent, args, ctx) -> value or {__type, ...} wrapper.
function wrapRepo(repo) { return { __type: 'Repository', repo }; }
function wrapIssue(repo, issue) { return { __type: 'Issue', repo, issue }; }
function wrapPull(repo, pull) { return { __type: 'PullRequest', repo, pull }; }
function wrapUser(login) { return { __type: 'User', login }; }

const GQL_FIELDS = {
  Query: {
    viewer: () => wrapUser(VIEWER.login),
    repository: (_p, args) => {
      const repo = repoFromPath(args.owner, args.name);
      return repo ? wrapRepo(repo) : null;
    },
    node: (_p, args) => {
      const decoded = decodeGid(args.id);
      if (!decoded) return null;
      if (decoded.kind === 'R') {
        const [owner, name] = decoded.payload.split('/');
        const repo = repoFromPath(owner, name);
        return repo ? wrapRepo(repo) : null;
      }
      if (decoded.kind === 'I') {
        const [ownerName, num] = decoded.payload.split('#');
        const [owner, name] = ownerName.split('/');
        const repo = repoFromPath(owner, name);
        const issue = repo?.issues.get(Number(num));
        return issue ? wrapIssue(repo, issue) : null;
      }
      if (decoded.kind === 'P') {
        const [ownerName, num] = decoded.payload.split('#');
        const [owner, name] = ownerName.split('/');
        const repo = repoFromPath(owner, name);
        const pull = repo?.pulls.get(Number(num));
        return pull ? wrapPull(repo, pull) : null;
      }
      return null;
    },
    __type: (_p, args) => ({ __type: '__Type', name: args.name }),
    __schema: () => ({ __type: '__Schema' }),
  },
  Repository: {
    id: (p) => gid('R', `${p.repo.owner}/${p.repo.name}`),
    databaseId: (p) => p.repo.id,
    name: (p) => p.repo.name,
    nameWithOwner: (p) => `${p.repo.owner}/${p.repo.name}`,
    owner: (p) => wrapUser(p.repo.owner),
    defaultBranchRef: (p) => {
      const sha = p.repo.refs.get(`refs/heads/${p.repo.defaultBranch}`);
      return sha ? { __type: 'Ref', name: p.repo.defaultBranch, oid: sha } : null;
    },
    viewerPermission: () => 'ADMIN',
    hasIssuesEnabled: () => true,
    url: (p) => `https://example.invalid/${p.repo.owner}/${p.repo.name}`,
    description: (p) => p.repo.description,
    private: (p) => p.repo.private,
    createdAt: (p) => p.repo.createdAt,
    updatedAt: (p) => p.repo.updatedAt,
    issue: (p, args) => {
      const issue = p.repo.issues.get(args.number);
      return issue ? wrapIssue(p.repo, issue) : null;
    },
    issues: (p, args) => {
      let list = [...p.repo.issues.values()];
      if (Array.isArray(args.states) && args.states.length > 0) {
        const wanted = new Set(args.states.map((s) => String(s).toLowerCase()));
        list = list.filter((i) => wanted.has(i.state));
      }
      const orderBy = args.orderBy ?? {};
      const field = String(orderBy.field ?? 'CREATED_AT');
      const direction = String(orderBy.direction ?? 'ASC');
      list.sort((a, b) => {
        let cmp = 0;
        if (field === 'CREATED_AT' || field === 'UPDATED_AT') cmp = a.createdSeq - b.createdSeq;
        else cmp = a.number - b.number;
        if (cmp === 0) cmp = a.number - b.number;
        return direction === 'DESC' ? -cmp : cmp;
      });
      return issueConnection(p.repo, list, args);
    },
    pullRequests: (p, args) => {
      let list = [...p.repo.pulls.values()];
      if (Array.isArray(args.states) && args.states.length > 0) {
        const wanted = new Set(args.states.map((s) => String(s).toUpperCase()));
        list = list.filter((pr) => wanted.has(pr.state === 'open' ? 'OPEN' : pr.merged ? 'MERGED' : 'CLOSED'));
      }
      list.sort((a, b) => b.createdSeq - a.createdSeq);
      const first = typeof args.first === 'number' ? args.first : list.length;
      return { __type: 'PullRequestConnection', nodes: list.slice(0, first).map((pr) => wrapPull(p.repo, pr)) };
    },
    pullRequest: (p, args) => {
      const pull = p.repo.pulls.get(args.number);
      return pull ? wrapPull(p.repo, pull) : null;
    },
  },
  User: {
    id: (p) => gid('U', p.login),
    login: (p) => p.login,
    name: (p) => (p.login === VIEWER.login ? VIEWER.name : p.login),
    email: (p) => (p.login === VIEWER.login ? VIEWER.email : ''),
  },
  Issue: {
    id: (p) => p.issue.nodeId,
    number: (p) => p.issue.number,
    title: (p) => p.issue.title,
    state: (p) => p.issue.state.toUpperCase(),
    body: (p) => p.issue.body ?? '',
    url: (p) => `https://example.invalid/${p.repo.owner}/${p.repo.name}/issues/${p.issue.number}`,
    createdAt: (p) => p.issue.createdAt,
    updatedAt: (p) => p.issue.updatedAt,
    author: () => wrapUser(VIEWER.login),
    labels: (p) => ({ __type: 'LabelConnection', nodes: p.issue.labels.map((name) => ({ __type: 'Label', name })) }),
    comments: (p) => ({ __type: 'IssueCommentConnection', nodes: (p.repo.comments.get(p.issue.number) ?? []).map((c) => ({ __type: 'IssueComment', id: c.node_id, body: c.body })) }),
    closedAt: (p) => p.issue.closedAt,
    repository: (p) => wrapRepo(p.repo),
  },
  PullRequest: {
    id: (p) => p.pull.nodeId,
    number: (p) => p.pull.number,
    title: (p) => p.pull.title,
    body: (p) => p.pull.body ?? '',
    state: (p) => (p.pull.state === 'open' ? 'OPEN' : p.pull.merged ? 'MERGED' : 'CLOSED'),
    merged: (p) => p.pull.merged,
    mergeable: (p) => (pullConflict(p.repo, p.pull) ? 'CONFLICTING' : 'MERGEABLE'),
    headRefName: (p) => p.pull.head.ref,
    baseRefName: (p) => p.pull.base.ref,
    headRefOid: (p) => p.pull.head.sha,
    baseRefOid: (p) => p.pull.base.sha,
    files: (p, args) => {
      const first = typeof args.first === 'number' ? args.first : p.pull.files.length;
      return { __type: 'PullRequestChangedFileConnection', nodes: p.pull.files.slice(0, first).map((f) => ({ __type: 'PullRequestChangedFile', path: f.filename })) };
    },
    url: (p) => `https://example.invalid/${p.repo.owner}/${p.repo.name}/pull/${p.pull.number}`,
    createdAt: (p) => p.pull.createdAt,
    updatedAt: (p) => p.pull.updatedAt,
    mergedAt: (p) => p.pull.mergedAt,
    mergeCommit: (p) => (p.pull.mergeCommitSha ? { __type: 'Commit', oid: p.pull.mergeCommitSha } : null),
    author: () => wrapUser(VIEWER.login),
    repository: (p) => wrapRepo(p.repo),
  },
  Ref: {
    name: (p) => p.name,
    target: (p) => ({ __type: 'Commit', oid: p.oid }),
  },
  Commit: {
    oid: (p) => p.oid,
  },
  Label: { name: (p) => p.name },
  IssueComment: { id: (p) => p.id, body: (p) => p.body },
  PullRequestChangedFile: { path: (p) => p.path },
  IssueConnection: {
    nodes: (p) => p.nodes,
    pageInfo: (p) => p.pageInfo,
    totalCount: (p) => p.totalCount,
  },
  PullRequestConnection: {
    nodes: (p) => p.nodes,
    pageInfo: () => ({ __type: 'PageInfo', hasNextPage: false, endCursor: null }),
  },
  PullRequestChangedFileConnection: {
    nodes: (p) => p.nodes,
    pageInfo: () => ({ __type: 'PageInfo', hasNextPage: false, endCursor: null }),
  },
  LabelConnection: { nodes: (p) => p.nodes },
  IssueCommentConnection: { nodes: (p) => p.nodes },
  PageInfo: {
    hasNextPage: (p) => p.hasNextPage,
    endCursor: (p) => p.endCursor,
  },
  __Type: {
    name: (p) => p.name,
    fields: (p) => {
      const map = { Issue: GQL_ISSUE_FIELDS, PullRequest: GQL_PR_FIELDS, Repository: GQL_REPO_FIELDS, User: ['id', 'login', 'name', 'email'] };
      const list = map[p.name];
      if (!list) return null;
      return list.map((name) => ({ __type: '__Field', name }));
    },
    enumValues: (p) => {
      if (p.name === 'SearchType') return GQL_SEARCH_ENUMS.map((name) => ({ __type: '__EnumValue', name }));
      return null;
    },
  },
  __Field: { name: (p) => p.name },
  __EnumValue: { name: (p) => p.name },
  __Schema: {},
  Mutation: {
    createIssue: (_p, args) => {
      const input = args.input ?? {};
      const decoded = decodeGid(input.repositoryId);
      if (!decoded || decoded.kind !== 'R') throw new Error('createIssue: unknown repositoryId');
      const [owner, name] = decoded.payload.split('/');
      const repo = repoFromPath(owner, name);
      if (!repo) throw new Error('createIssue: repository not found');
      const issue = createIssueInRepo(repo, { title: input.title ?? '', body: input.body ?? '' });
      return { __type: 'CreateIssuePayload', issue: wrapIssue(repo, issue) };
    },
    closeIssue: (_p, args) => {
      const input = args.input ?? {};
      const decoded = decodeGid(input.issueId);
      if (!decoded || decoded.kind !== 'I') throw new Error('closeIssue: unknown issueId');
      const [ownerName, num] = decoded.payload.split('#');
      const [owner, name] = ownerName.split('/');
      const repo = repoFromPath(owner, name);
      const issue = repo?.issues.get(Number(num));
      if (!issue) throw new Error('closeIssue: issue not found');
      issue.state = 'closed';
      issue.closedAt = nextIso();
      issue.updatedAt = nextIso();
      return { __type: 'CloseIssuePayload', issue: wrapIssue(repo, issue) };
    },
    createPullRequest: (_p, args) => {
      const input = args.input ?? {};
      const decoded = decodeGid(input.repositoryId);
      if (!decoded || decoded.kind !== 'R') throw new Error('createPullRequest: unknown repositoryId');
      const [owner, name] = decoded.payload.split('/');
      const repo = repoFromPath(owner, name);
      if (!repo) throw new Error('createPullRequest: repository not found');
      const pull = createPullInRepo(repo, { title: input.title ?? '', body: input.body ?? '', head: input.headRefName, base: input.baseRefName });
      return { __type: 'CreatePullRequestPayload', pullRequest: wrapPull(repo, pull) };
    },
    mergePullRequest: (_p, args) => {
      const input = args.input ?? {};
      const decoded = decodeGid(input.pullRequestId);
      if (!decoded || decoded.kind !== 'P') throw new Error('mergePullRequest: unknown pullRequestId');
      const [ownerName, num] = decoded.payload.split('#');
      const [owner, name] = ownerName.split('/');
      const repo = repoFromPath(owner, name);
      const pull = repo?.pulls.get(Number(num));
      if (!pull) throw new Error('mergePullRequest: pull request not found');
      if (pull.state !== 'open') throw new Error('mergePullRequest: pull request is not open');
      const oid = mergePull(repo, pull);
      if (!oid) throw new Error('mergePullRequest: merge conflict');
      return { __type: 'MergePullRequestPayload', pullRequest: wrapPull(repo, pull) };
    },
    addComment: (_p, args) => {
      const input = args.input ?? {};
      const decoded = decodeGid(input.subjectId);
      if (!decoded || decoded.kind !== 'I') throw new Error('addComment: unknown subjectId');
      const [ownerName, num] = decoded.payload.split('#');
      const [owner, name] = ownerName.split('/');
      const repo = repoFromPath(owner, name);
      const issue = repo?.issues.get(Number(num));
      if (!issue) throw new Error('addComment: issue not found');
      const issueNumber = Number(num);
      const comment = { id: commentIdSeq++, node_id: gid('C', `${owner}/${name}#${issueNumber}:${commentIdSeq}`), body: input.body ?? '', user: { login: VIEWER.login, id: VIEWER.id }, created_at: nextIso(), updated_at: nextIso() };
      if (!repo.comments.has(issueNumber)) repo.comments.set(issueNumber, []);
      repo.comments.get(issueNumber).push(comment);
      return { __type: 'AddCommentPayload', commentEdge: { __type: 'IssueCommentEdge', node: { __type: 'IssueComment', id: comment.node_id, body: comment.body } } };
    },
  },
  CreateIssuePayload: { issue: (p) => p.issue },
  CloseIssuePayload: { issue: (p) => p.issue },
  CreatePullRequestPayload: { pullRequest: (p) => p.pullRequest },
  MergePullRequestPayload: { pullRequest: (p) => p.pullRequest },
  AddCommentPayload: { commentEdge: (p) => p.commentEdge },
  IssueCommentEdge: { node: (p) => p.node },
};

function issueConnection(repo, list, args) {
  const first = typeof args.first === 'number' ? args.first : list.length;
  let start = 0;
  if (typeof args.after === 'string' && args.after !== '') {
    try {
      const afterNum = Number(Buffer.from(args.after, 'base64url').toString('utf8').replace(/^c:/, ''));
      const idx = list.findIndex((i) => i.number === afterNum);
      if (idx >= 0) start = idx + 1;
    } catch { /* ignore a bad cursor */ }
  }
  const sliced = list.slice(start, start + first);
  const hasNextPage = start + sliced.length < list.length;
  const endCursor = sliced.length > 0 ? Buffer.from(`c:${sliced[sliced.length - 1].number}`, 'utf8').toString('base64url') : null;
  return {
    __type: 'IssueConnection',
    nodes: sliced.map((i) => wrapIssue(repo, i)),
    pageInfo: { __type: 'PageInfo', hasNextPage, endCursor },
    totalCount: list.length,
  };
}

function gqlTypeOf(value) {
  if (value && typeof value === 'object' && typeof value.__type === 'string') return value.__type;
  return null;
}

function executeSelections(parent, typeName, selections, variables, fragments, errors) {
  const out = {};
  for (const sel of selections) {
    if (sel.kind === 'spread') {
      const frag = fragments[sel.name];
      if (frag) Object.assign(out, executeSelections(parent, typeName, frag.selections, variables, fragments, errors));
      continue;
    }
    if (sel.kind === 'inline') {
      Object.assign(out, executeSelections(parent, typeName, sel.selections, variables, fragments, errors));
      continue;
    }
    const resolvers = GQL_FIELDS[typeName] ?? {};
    if (sel.name === '__typename') { out[sel.alias] = typeName; continue; }
    const resolve = resolvers[sel.name];
    if (!resolve) {
      errors.push({ message: `Cannot query field "${sel.name}" on type "${typeName}".` });
      continue;
    }
    let value;
    try {
      value = resolve(parent, gqlArgs(sel, variables));
    } catch (err) {
      errors.push({ message: err.message });
      continue;
    }
    if (value === null || value === undefined) { out[sel.alias] = null; continue; }
    if (sel.selections) {
      if (Array.isArray(value)) {
        out[sel.alias] = value.map((item) => {
          const t = gqlTypeOf(item);
          return t ? executeSelections(item, t, sel.selections, variables, fragments, errors) : item;
        });
      } else {
        const t = gqlTypeOf(value);
        out[sel.alias] = t ? executeSelections(value, t, sel.selections, variables, fragments, errors) : value;
      }
    } else {
      out[sel.alias] = value;
    }
  }
  return out;
}

function executeGraphQL(queryText, variables = {}, operationName = undefined) {
  let definitions;
  try {
    definitions = gqlParse(queryText);
  } catch (err) {
    return { data: null, errors: [{ message: err.message }] };
  }
  const fragments = {};
  for (const d of definitions) if (d.kind === 'fragment') fragments[d.name] = d;
  const operations = definitions.filter((d) => d.kind === 'operation');
  const op = operationName ? operations.find((o) => o.name === operationName) : operations[0];
  if (!op) return { data: null, errors: [{ message: 'No operation found' }] };
  const vars = { ...variables };
  for (const def of op.varDefs) {
    if (vars[def.name] === undefined && def.defaultValue !== undefined) vars[def.name] = gqlValue(def.defaultValue, {});
  }
  const rootType = op.operation === 'mutation' ? 'Mutation' : 'Query';
  const errors = [];
  const data = executeSelections({}, rootType, op.selections, vars, fragments, errors);
  const result = { data };
  if (errors.length > 0) result.errors = errors;
  return result;
}

// ---------------------------------------------------------------- MCP
// JSON-RPC 2.0 Streamable HTTP. Modern era 2026-07-28 (server/discover) plus
// legacy initialize for older clients. Tools act on the same store as REST.

const MCP_TOOLS = [
  {
    name: 'create_repo',
    description: 'Create a new repository for the authenticated user.',
    inputSchema: { type: 'object', properties: { name: { type: 'string', description: 'Repository name' }, description: { type: 'string', description: 'Repository description' }, private: { type: 'boolean', description: 'Whether the repository is private' } }, required: ['name'] },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' }, full_name: { type: 'string', description: 'Full repository name owner/repo' } }, required: ['owner', 'repo'] },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' }, full_name: { type: 'string', description: 'Full repository name owner/repo' }, title: { type: 'string', description: 'Issue title' }, body: { type: 'string', description: 'Issue body' } }, required: ['owner', 'repo', 'title'] },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' }, full_name: { type: 'string', description: 'Full repository name owner/repo' }, state: { type: 'string', description: 'Issue state: open, closed, or all' } }, required: ['owner', 'repo'] },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request in a repository.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' }, full_name: { type: 'string', description: 'Full repository name owner/repo' }, title: { type: 'string', description: 'Pull request title' }, head: { type: 'string', description: 'Head branch name' }, base: { type: 'string', description: 'Base branch name' }, body: { type: 'string', description: 'Pull request body' } }, required: ['owner', 'repo', 'title', 'head', 'base'] },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request in a repository using a squash merge.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner login' }, repo: { type: 'string', description: 'Repository name' }, full_name: { type: 'string', description: 'Full repository name owner/repo' }, pull_number: { type: 'integer', description: 'Pull request number' } }, required: ['owner', 'repo', 'pull_number'] },
  },
];

function mcpResult(id, result) {
  return { jsonrpc: '2.0', id, result };
}
function mcpError(id, code, message) {
  return { jsonrpc: '2.0', id, error: { code, message } };
}
function mcpToolText(result) {
  return { content: [{ type: 'text', text: JSON.stringify(result) }], structuredContent: result };
}
function mcpToolError(message) {
  return { content: [{ type: 'text', text: message }], isError: true };
}

function splitFullName(args) {
  if ((!args.owner || !args.repo) && typeof args.full_name === 'string') {
    const parts = args.full_name.split('/');
    if (parts.length === 2) { args.owner = parts[0]; args.repo = parts[1]; }
  }
  return args;
}

async function mcpCallTool(toolName, args) {
  const name = String(toolName ?? '').toLowerCase();
  const tool = MCP_TOOLS.find((t) => t.name === name || name.endsWith(t.name) || t.name.endsWith(name));
  if (!tool) throw { code: -32601, message: `Method not found: ${toolName}` };
  const a = splitFullName({ ...(args ?? {}) });
  const missing = (tool.inputSchema.required ?? []).filter((k) => a[k] === undefined || a[k] === null || a[k] === '');
  if (missing.length > 0) {
    return mcpToolError(`Missing required argument(s): ${missing.join(', ')}`);
  }
  switch (tool.name) {
    case 'create_repo': {
      if (getRepo(VIEWER.login, a.name)) return mcpToolError('Repository already exists');
      const repo = newRepo(VIEWER.login, a.name, { description: a.description ?? '', private: a.private ?? false });
      repos.set(repoKey(repo.owner, repo.name), repo);
      return mcpToolText(repoJson(repo));
    }
    case 'get_repo': {
      const repo = repoFromPath(a.owner, a.repo);
      if (!repo) return mcpToolError('Not Found');
      return mcpToolText(repoJson(repo));
    }
    case 'create_issue': {
      const repo = repoFromPath(a.owner, a.repo);
      if (!repo) return mcpToolError('Not Found');
      const issue = createIssueInRepo(repo, { title: a.title, body: a.body ?? '' });
      return mcpToolText(issueJson(repo, issue));
    }
    case 'list_issues': {
      const repo = repoFromPath(a.owner, a.repo);
      if (!repo) return mcpToolError('Not Found');
      const state = a.state ?? 'open';
      let list = [...repo.issues.values()];
      if (state !== 'all') list = list.filter((i) => i.state === state);
      list.sort((x, y) => y.createdSeq - x.createdSeq);
      return mcpToolText(list.map((i) => issueJson(repo, i)));
    }
    case 'create_pull_request': {
      const repo = repoFromPath(a.owner, a.repo);
      if (!repo) return mcpToolError('Not Found');
      if (!repo.refs.has(`refs/heads/${a.head}`)) return mcpToolError('Head branch does not exist');
      if (!repo.refs.has(`refs/heads/${a.base}`)) return mcpToolError('Base branch does not exist');
      const pull = createPullInRepo(repo, { title: a.title, body: a.body ?? '', head: a.head, base: a.base });
      return mcpToolText(pullJson(repo, pull));
    }
    case 'merge_pull_request': {
      const repo = repoFromPath(a.owner, a.repo);
      if (!repo) return mcpToolError('Not Found');
      const pull = repo.pulls.get(Number(a.pull_number));
      if (!pull) return mcpToolError('Not Found');
      if (pull.state !== 'open') return mcpToolError('Pull request is not open');
      const oid = mergePull(repo, pull);
      if (!oid) return mcpToolError('Merge conflict');
      return mcpToolText({ sha: oid, merged: true, message: 'Pull Request successfully merged' });
    }
    default:
      throw { code: -32601, message: `Method not found: ${toolName}` };
  }
}

async function handleMcp(req, res) {
  if (!authed(req)) { sendJson(res, 401, { message: 'Requires authentication' }); return; }
  const body = await readBody(req);
  let rpc;
  try {
    rpc = JSON.parse(body.toString('utf8'));
  } catch {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  if (!rpc || typeof rpc !== 'object' || typeof rpc.method !== 'string') {
    sendJson(res, 400, { jsonrpc: '2.0', id: rpc?.id ?? null, error: { code: -32600, message: 'Invalid Request' } });
    return;
  }
  const id = rpc.id ?? null;
  const method = rpc.method;
  const params = rpc.params ?? {};
  try {
    if (method === 'server/discover') {
      sendJson(res, 200, mcpResult(id, {
        supportedVersions: ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'],
        capabilities: { tools: {} },
        serverInfo: { name: 'github-forge', version: '1.0.0' },
      }));
      return;
    }
    if (method === 'initialize') {
      const requested = params.protocolVersion;
      const known = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];
      const protocolVersion = known.includes(requested) ? requested : '2025-11-25';
      sendJson(res, 200, mcpResult(id, {
        protocolVersion,
        capabilities: { tools: {} },
        serverInfo: { name: 'github-forge', version: '1.0.0' },
      }));
      return;
    }
    if (method === 'notifications/initialized' || method.startsWith('notifications/')) {
      res.writeHead(202, { 'x-github-request-id': `req-${++requestSeq}` });
      res.end();
      return;
    }
    if (method === 'tools/list') {
      sendJson(res, 200, mcpResult(id, { tools: MCP_TOOLS }));
      return;
    }
    if (method === 'tools/call') {
      const result = await mcpCallTool(params.name, params.arguments ?? {});
      sendJson(res, 200, mcpResult(id, result));
      return;
    }
    sendJson(res, 200, mcpError(id, -32601, `Method not found: ${method}`));
  } catch (err) {
    if (err && typeof err === 'object' && typeof err.code === 'number') {
      sendJson(res, 200, mcpError(id, err.code, err.message));
      return;
    }
    sendJson(res, 200, mcpError(id, -32603, err instanceof Error ? err.message : 'Internal error'));
  }
}

// ---------------------------------------------------------------- Git smart HTTP
// Protocol v0 and v2, shaped to what the kit's own git-client.ts expects:
//  - v2 ls-refs / fetch responses carry NO `version 2` line (the client rejects it).
//  - fetch v2 sections are delimited by 0001 packets: acknowledgments, shallow-info, packfile.
//  - packs are always full (no deltas); the client resolves thin packs only when it must.

function pkt(data) {
  const b = typeof data === 'string' ? Buffer.from(data, 'utf8') : data;
  const h = Buffer.alloc(4);
  h.write((b.length + 4).toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([h, b]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');

function parsePktStream(buf) {
  const packets = [];
  let offset = 0;
  while (offset < buf.length) {
    if (offset + 4 > buf.length) return { packets, consumed: offset, error: 'truncated pkt-line' };
    const head = buf.subarray(offset, offset + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(head)) return { packets, consumed: offset, error: `bad pkt-line length ${JSON.stringify(head)}` };
    const len = Number.parseInt(head, 16);
    if (len === 0) { packets.push({ kind: 'flush' }); offset += 4; continue; }
    if (len === 1) { packets.push({ kind: 'delim' }); offset += 4; continue; }
    if (len === 2) { packets.push({ kind: 'response-end' }); offset += 4; continue; }
    if (len === 3) return { packets, consumed: offset, error: 'bad pkt-line length 0003' };
    if (offset + len > buf.length) return { packets, consumed: offset, error: 'truncated pkt-line' };
    packets.push({ kind: 'data', data: buf.subarray(offset + 4, offset + len) });
    offset += len;
  }
  return { packets, consumed: offset, error: null };
}

function sidebandPackets(band, data) {
  const out = [];
  for (let i = 0; i < data.length; i += 65515) {
    out.push(pkt(Buffer.concat([Buffer.from([band]), data.subarray(i, i + 65515)])));
  }
  if (data.length === 0) out.push(pkt(Buffer.from([band])));
  return out;
}

function listRefsWithPeel(repo) {
  const entries = [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
  const out = [];
  for (const [name, oid] of entries) {
    const entry = { oid, name };
    if (name.startsWith('refs/tags/')) {
      const obj = lookup(repo, oid);
      if (obj && obj.type === 'tag') entry.peeled = parseTag(obj.data).object;
    }
    out.push(entry);
  }
  return out;
}

const UPLOAD_CAPS = 'symref=HEAD:refs/heads/main agent=github-forge/1.0 side-band-64k thin-pack ofs-delta shallow multi_ack';
const RECEIVE_CAPS = 'report-status report-status-v2 side-band-64k delete-refs ofs-delta agent=github-forge/1.0';

function handleInfoRefs(req, res, repo, service) {
  const v2 = service === 'git-upload-pack' && (req.headers['git-protocol'] ?? '') === 'version=2';
  if (v2) {
    const lines = [
      pkt('version 2\n'),
      pkt('ls-refs=unborn\n'),
      pkt('fetch=shallow filter\n'),
      pkt('object-format=sha1\n'),
      pkt('agent=github-forge/1.0\n'),
      PKT_FLUSH,
    ];
    sendBytes(res, 200, Buffer.concat(lines), `application/x-${service}-advertisement`);
    return;
  }
  // v0 advertisement.
  const refs = listRefsWithPeel(repo);
  const parts = [];
  parts.push(pkt('# service=git-upload-pack\n'.replace('git-upload-pack', service)));
  parts.push(PKT_FLUSH);
  const caps = service === 'git-upload-pack' ? UPLOAD_CAPS : RECEIVE_CAPS;
  if (refs.length === 0) {
    parts.push(pkt(`${ZERO_OID} capabilities^{}\0${caps}\n`));
  } else {
    const headOid = repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? ZERO_OID;
    parts.push(pkt(`${headOid} HEAD\0${caps}\n`));
    for (const ref of refs) {
      parts.push(pkt(`${ref.oid} ${ref.name}\n`));
      if (ref.peeled) parts.push(pkt(`${ref.peeled} ${ref.name}^{}\n`));
    }
  }
  parts.push(PKT_FLUSH);
  sendBytes(res, 200, Buffer.concat(parts), `application/x-${service}-advertisement`);
}

function collectTreeObjects(repo, treeOid, out) {
  if (out.has(treeOid)) return;
  const obj = lookup(repo, treeOid);
  if (!obj || obj.type !== 'tree') return;
  out.add(treeOid);
  for (const entry of parseTree(obj.data)) {
    if (entry.mode === '40000') collectTreeObjects(repo, entry.oid, out);
    else if (entry.mode !== '160000') out.add(entry.oid);
  }
}

function peelToCommit(repo, oid) {
  const obj = lookup(repo, oid);
  if (!obj) return null;
  if (obj.type === 'tag') return parseTag(obj.data).object;
  if (obj.type === 'commit') return oid;
  return null;
}

function fetchPlan(repo, wants, haves, depth, oldShallow) {
  const haveSet = new Set();
  for (const h of haves ?? []) {
    for (const o of collectReachable([h], (oid) => lookup(repo, oid), { allowMissing: true })) haveSet.add(o);
  }
  // A shallow boundary is a commit the client HAS but whose parents it does NOT have:
  // drop everything reachable from each boundary's parents out of the have-set, or a
  // deepen would wrongly conclude the parent is already on the client.
  for (const b of oldShallow ?? []) {
    const boundary = lookup(repo, b);
    if (!boundary || boundary.type !== 'commit') continue;
    for (const parent of parseCommit(boundary.data).parents) {
      for (const o of collectReachable([parent], (oid) => lookup(repo, oid), { allowMissing: true })) haveSet.delete(o);
    }
  }
  const send = new Set();
  const includedCommits = new Map();
  if (depth == null) {
    for (const o of collectReachable(wants, (oid) => lookup(repo, oid), { allowMissing: true })) {
      send.add(o);
      const obj = lookup(repo, o);
      if (obj && obj.type === 'commit') includedCommits.set(o, 0);
    }
  } else {
    const queue = [];
    const seen = new Set();
    for (const w of wants) {
      const c = peelToCommit(repo, w);
      if (c) queue.push([c, 0]);
    }
    while (queue.length > 0) {
      const [oid, d] = queue.shift();
      if (seen.has(oid)) continue;
      seen.add(oid);
      const obj = lookup(repo, oid);
      if (!obj || obj.type !== 'commit') continue;
      includedCommits.set(oid, d);
      if (d + 1 < depth) {
        for (const p of parseCommit(obj.data).parents) queue.push([p, d + 1]);
      }
    }
    for (const oid of includedCommits.keys()) {
      send.add(oid);
      const tree = parseCommit(lookup(repo, oid).data).tree;
      collectTreeObjects(repo, tree, send);
    }
  }
  for (const o of haveSet) send.delete(o);
  const shallow = [];
  for (const oid of includedCommits.keys()) {
    const parents = parseCommit(lookup(repo, oid).data).parents;
    if (parents.length > 0 && parents.some((p) => !includedCommits.has(p))) shallow.push(oid);
  }
  const unshallow = (oldShallow ?? []).filter((b) => {
    if (!includedCommits.has(b)) return false;
    const obj = lookup(repo, b);
    if (!obj || obj.type !== 'commit') return false;
    return parseCommit(obj.data).parents.every((p) => includedCommits.has(p));
  });
  const objects = [...send].map((oid) => {
    const obj = lookup(repo, oid);
    return { type: obj.type, data: obj.data };
  });
  return { objects, shallow, unshallow };
}

function handleLsRefsV2(req, res, repo, packets) {
  let peel = false;
  let symrefs = false;
  let unborn = false;
  const prefixes = [];
  let afterDelim = false;
  for (const p of packets) {
    if (p.kind === 'delim') { afterDelim = true; continue; }
    if (p.kind === 'flush') break;
    if (p.kind !== 'data') continue;
    const line = p.data.toString('utf8').replace(/\n$/, '');
    if (!afterDelim) continue;
    if (line === 'peel') peel = true;
    else if (line === 'symrefs') symrefs = true;
    else if (line === 'unborn') unborn = true;
    else if (line.startsWith('ref-prefix ')) prefixes.push(line.slice('ref-prefix '.length));
  }
  const refs = listRefsWithPeel(repo);
  const parts = [];
  if (refs.length > 0) {
    const headOid = repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? null;
    if (prefixes.length === 0) {
      if (headOid) {
        parts.push(pkt(`${headOid} HEAD${symrefs ? ' symref-target:refs/heads/main' : ''}\n`));
      } else if (unborn) {
        parts.push(pkt(`unborn HEAD${symrefs ? ' symref-target:refs/heads/main' : ''}\n`));
      }
    }
    for (const ref of refs) {
      if (prefixes.length > 0 && !prefixes.some((pre) => ref.name.startsWith(pre))) continue;
      let line = `${ref.oid} ${ref.name}`;
      if (peel && ref.peeled) line += ` peeled:${ref.peeled}`;
      parts.push(pkt(`${line}\n`));
    }
  }
  parts.push(PKT_FLUSH);
  sendBytes(res, 200, Buffer.concat(parts), 'application/x-git-upload-pack-result');
}

function handleFetchV2(req, res, repo, packets) {
  const wants = [];
  const haves = [];
  const shallowIn = [];
  let depth = null;
  let afterDelim = false;
  for (const p of packets) {
    if (p.kind === 'delim') { afterDelim = true; continue; }
    if (p.kind === 'flush') break;
    if (p.kind !== 'data') continue;
    const line = p.data.toString('utf8').replace(/\n$/, '');
    if (!afterDelim) continue;
    if (line.startsWith('want ')) wants.push(line.slice(5).trim());
    else if (line.startsWith('have ')) haves.push(line.slice(5).trim());
    else if (line.startsWith('shallow ')) shallowIn.push(line.slice(8).trim());
    else if (line.startsWith('deepen ')) depth = Number.parseInt(line.slice(7).trim(), 10);
  }
  const plan = fetchPlan(repo, wants, haves, depth, shallowIn);
  const pack = writePack(plan.objects);
  const parts = [];
  parts.push(pkt('acknowledgments\n'));
  parts.push(pkt('NAK\n'));
  parts.push(PKT_DELIM);
  if (plan.shallow.length > 0 || plan.unshallow.length > 0) {
    parts.push(pkt('shallow-info\n'));
    for (const oid of plan.shallow) parts.push(pkt(`shallow ${oid}\n`));
    for (const oid of plan.unshallow) parts.push(pkt(`unshallow ${oid}\n`));
    parts.push(PKT_DELIM);
  }
  parts.push(pkt('packfile\n'));
  for (const chunk of sidebandPackets(1, pack)) parts.push(chunk);
  parts.push(PKT_FLUSH);
  sendBytes(res, 200, Buffer.concat(parts), 'application/x-git-upload-pack-result');
}

function handleFetchV0(req, res, repo, packets) {
  const wants = [];
  const haves = [];
  const shallowIn = [];
  let depth = null;
  let section = 0; // 0 = wants, 1 = haves
  for (const p of packets) {
    if (p.kind === 'flush') { section = 1; continue; }
    if (p.kind !== 'data') continue;
    const line = p.data.toString('utf8').replace(/\n$/, '');
    if (section === 0) {
      if (line.startsWith('want ')) wants.push(line.slice(5).split(' ')[0].trim());
      else if (line.startsWith('shallow ')) shallowIn.push(line.slice(8).trim());
      else if (line.startsWith('deepen ')) depth = Number.parseInt(line.slice(7).trim(), 10);
    } else {
      if (line.startsWith('have ')) haves.push(line.slice(5).trim());
    }
  }
  const plan = fetchPlan(repo, wants, haves, depth, shallowIn);
  const pack = writePack(plan.objects);
  const parts = [];
  parts.push(pkt('NAK\n'));
  for (const oid of plan.shallow) parts.push(pkt(`shallow ${oid}\n`));
  for (const oid of plan.unshallow) parts.push(pkt(`unshallow ${oid}\n`));
  for (const chunk of sidebandPackets(1, pack)) parts.push(chunk);
  parts.push(PKT_FLUSH);
  sendBytes(res, 200, Buffer.concat(parts), 'application/x-git-upload-pack-result');
}

async function handleUploadPack(req, res, repo) {
  const body = await readBody(req);
  const parsed = parsePktStream(body);
  if (parsed.error) {
    sendBytes(res, 200, PKT_FLUSH, 'application/x-git-upload-pack-result');
    return;
  }
  const v2 = (req.headers['git-protocol'] ?? '') === 'version=2';
  if (v2) {
    const first = parsed.packets.find((p) => p.kind === 'data');
    const command = first ? first.data.toString('utf8').replace(/\n$/, '') : '';
    if (command === 'command=ls-refs') { handleLsRefsV2(req, res, repo, parsed.packets); return; }
    if (command === 'command=fetch') { handleFetchV2(req, res, repo, parsed.packets); return; }
    sendBytes(res, 200, PKT_FLUSH, 'application/x-git-upload-pack-result');
    return;
  }
  handleFetchV0(req, res, repo, parsed.packets);
}

async function handleReceivePack(req, res, repo) {
  const body = await readBody(req);
  const report = (unpackOk, lines) => {
    const text = pkt(`unpack ${unpackOk ? 'ok' : lines[0] ?? 'error'}\n`);
    const rest = lines.slice(unpackOk ? 0 : 1).map((l) => pkt(`${l}\n`));
    const stream = Buffer.concat([text, ...rest]);
    const parts = [...sidebandPackets(1, stream), PKT_FLUSH];
    sendBytes(res, 200, Buffer.concat(parts), 'application/x-git-receive-pack-result');
  };
  // Parse command pkt-lines one at a time until the flush; everything after the flush is the
  // raw pack (its bytes are not pkt-lines and must never be parsed as such).
  const commands = [];
  let offset = 0;
  let sawFlush = false;
  let parseError = null;
  while (offset < body.length) {
    if (offset + 4 > body.length) { parseError = 'truncated pkt-line'; break; }
    const head = body.subarray(offset, offset + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(head)) { parseError = `bad pkt-line length ${JSON.stringify(head)}`; break; }
    const len = Number.parseInt(head, 16);
    if (len === 0) { offset += 4; sawFlush = true; break; }
    if (len === 1 || len === 2) { offset += 4; continue; }
    if (len === 3) { parseError = 'bad pkt-line length 0003'; break; }
    if (offset + len > body.length) { parseError = 'truncated pkt-line'; break; }
    const line = body.subarray(offset + 4, offset + len).toString('utf8').replace(/\n$/, '');
    const nul = line.indexOf('\0');
    const clean = nul >= 0 ? line.slice(0, nul) : line;
    const parts = clean.split(' ');
    if (parts.length >= 3) commands.push({ oldOid: parts[0], newOid: parts[1], ref: parts[2] });
    offset += len;
  }
  if (parseError || !sawFlush) {
    report(false, [parseError ?? 'missing flush after command list']);
    return;
  }
  const packBytes = body.subarray(offset);
  let unpackError = null;
  if (packBytes.length > 0) {
    try {
      const read = readPack(packBytes);
      for (const [oid, obj] of read.objects) {
        if (!lookup(repo, oid)) putObject(repo, obj.type, obj.data);
      }
    } catch (err) {
      unpackError = err instanceof Error ? err.message : 'pack parse failed';
    }
  }
  const lines = [];
  if (unpackError) {
    for (const c of commands) lines.push(`ng ${c.ref} unpack failed: ${unpackError}`);
    report(false, [unpackError, ...lines]);
    return;
  }
  for (const c of commands) {
    if (c.newOid === ZERO_OID) {
      if (!repo.refs.has(c.ref)) { lines.push(`ng ${c.ref} remote ref does not exist`); continue; }
      repo.refs.delete(c.ref);
      lines.push(`ok ${c.ref}`);
      continue;
    }
    if (c.oldOid === ZERO_OID) {
      if (repo.refs.has(c.ref)) { lines.push(`ng ${c.ref} reference already exists`); continue; }
      if (!lookup(repo, c.newOid)) { lines.push(`ng ${c.ref} object not found`); continue; }
      repo.refs.set(c.ref, c.newOid);
      lines.push(`ok ${c.ref}`);
      continue;
    }
    const current = repo.refs.get(c.ref);
    if (!current) { lines.push(`ng ${c.ref} remote ref does not exist`); continue; }
    if (current !== c.oldOid) { lines.push(`ng ${c.ref} non-fast-forward`); continue; }
    if (!isAncestor(c.oldOid, c.newOid, (oid) => lookup(repo, oid))) { lines.push(`ng ${c.ref} non-fast-forward`); continue; }
    repo.refs.set(c.ref, c.newOid);
    lines.push(`ok ${c.ref}`);
  }
  report(true, lines);
}

async function handleGit(req, res, path) {
  const m = /^\/([^/]+)\/([^/]+)\.git\/(.*)$/.exec(path);
  if (!m) return false;
  const owner = decodeSegment(m[1]);
  const name = decodeSegment(m[2]);
  const tail = m[3];
  const repo = repoFromPath(owner, name);
  if (tail === 'info/refs') {
    const service = new URL(req.url, 'http://localhost').searchParams.get('service');
    if (!repo) { errJson(res, 404, 'Not Found'); return true; }
    if (service !== 'git-upload-pack' && service !== 'git-receive-pack') { errJson(res, 404, 'Not Found'); return true; }
    handleInfoRefs(req, res, repo, service);
    return true;
  }
  if (tail === 'git-upload-pack' && req.method === 'POST') {
    if (!repo) { errJson(res, 404, 'Not Found'); return true; }
    await handleUploadPack(req, res, repo);
    return true;
  }
  if (tail === 'git-receive-pack' && req.method === 'POST') {
    if (!repo) { errJson(res, 404, 'Not Found'); return true; }
    await handleReceivePack(req, res, repo);
    return true;
  }
  return false;
}

// ---------------------------------------------------------------- App

export function createApp() {
  return async (req, res) => {
    try {
      const url = new URL(req.url ?? '/', 'http://localhost');
      const path = url.pathname;
      const method = req.method ?? 'GET';
      const query = url.searchParams;

      if (path === '/healthz' && method === 'GET') {
        sendJson(res, 200, { ok: true });
        return;
      }
      if (path === '/mcp' && method === 'POST') {
        await handleMcp(req, res);
        return;
      }
      if (path === '/api/graphql' && method === 'POST') {
        if (!authed(req)) { sendJson(res, 401, { message: 'Requires authentication' }); return; }
        const body = await readBody(req);
        let doc;
        try {
          doc = JSON.parse(body.toString('utf8'));
        } catch {
          sendJson(res, 400, { errors: [{ message: 'Request body is not valid JSON' }] });
          return;
        }
        if (Array.isArray(doc)) {
          const results = doc.map((d) => executeGraphQL(d?.query ?? '', d?.variables ?? {}, d?.operationName));
          sendJson(res, 200, results);
          return;
        }
        sendJson(res, 200, executeGraphQL(doc?.query ?? '', doc?.variables ?? {}, doc?.operationName));
        return;
      }
      if (path === '/api/v3' || path.startsWith('/api/v3/')) {
        if (!authed(req)) { sendJson(res, 401, { message: 'Requires authentication' }); return; }
        const handled = await handleRest(req, res, path, method, query);
        if (!handled) errJson(res, 404, 'Not Found');
        return;
      }
      if (await handleGit(req, res, path)) return;

      errJson(res, 404, 'Not Found');
    } catch (err) {
      console.error('forge error:', err);
      if (!res.headersSent) {
        try { errJson(res, 500, 'Internal Server Error'); } catch { /* socket gone */ }
      }
    }
  };
}
