#!/usr/bin/env node
// Guards for a pull request that adds one proof file. Used by both workflows, before anything
// is built. Plain node, no dependencies. Every value this script hands back to the shell has
// passed a strict pattern, so the shell never sees free text from a pull request.
//
//   node outside-guard.mjs pr <pr.json> <files.json> <tree.json> <repo> <default branch> <out dir>
//   node outside-guard.mjs gap <gaps.json> <gap id> <file path> <out dir>
//   node outside-guard.mjs gap-of-file <gaps.json> <file path> <out dir>
//   node outside-guard.mjs imports <lean file> <imports.json> [build-imports.json]
//   node outside-guard.mjs closure <base dir> <imports.json> <judged file path> <out dir>
//
// Exit 0: the guard holds. Exit 1: REFUSED, with one line saying why. Exit 3: bad usage.
import { lstatSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

export const FILE_RE = /^lean\/(?:PEqualNP\/Outside\/L_[a-z0-9_]+|Conjectures\/[A-Z][A-Za-z0-9]*\/[A-Z][A-Za-z0-9]*)\.lean$/;
export const GAP_RE = /^L-[a-z0-9]+(-[a-z0-9]+)*$/;
export const MODULE_RE = /^(?:PEqualNP|Conjectures)(\.[A-Za-z][A-Za-z0-9_]*)+$/;
export const MAX_BYTES = 2 * 1024 * 1024;
const SHA_RE = /^[0-9a-f]{40}$/;
const LOGIN_RE = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})(\[bot\])?$/;

class Refused extends Error {}
const refuse = (why) => { throw new Refused(why); };
const json = (path) => { try { return JSON.parse(readFileSync(path, 'utf8')); } catch { return refuse(`${path} is not JSON`); } };
const moduleOf = (file) => file.slice('lean/'.length, -'.lean'.length).split('/').join('.');

// The pull request must add exactly one file, the allowed kind, as a plain file, and nothing else.
// Read from the API's own answers: the pull request, its file list, the tree of its head commit.
export function checkPr(pr, files, tree, repo, defaultBranch) {
  if (pr?.state !== 'open') refuse('the pull request is not open');
  if (pr.base?.repo?.full_name !== repo) refuse('the pull request is not against this repository');
  if (pr.base?.ref !== defaultBranch) refuse(`the pull request is not against ${defaultBranch}`);
  const head = pr.head?.sha;
  if (!SHA_RE.test(head ?? '')) refuse('the pull request has no head commit');
  const author = pr.user?.login;
  if (!LOGIN_RE.test(author ?? '')) refuse('the pull request author is not a plain account name');
  // changed_files is the whole count, so a long file list cannot hide a second file on another page.
  if (pr.changed_files !== 1) refuse(`the pull request changes ${pr.changed_files} files; it must add exactly one`);
  if (!Array.isArray(files) || files.length !== 1) refuse('the pull request must add exactly one file');
  const f = files[0];
  if (typeof f.filename !== 'string' || !FILE_RE.test(f.filename)) refuse('the one file must be a registered community proof path');
  if (f.status !== 'added') refuse(`the file must be added, not ${f.status}`);
  if (!SHA_RE.test(f.sha ?? '')) refuse('the file list names no content hash');
  // The tree says what kind of entry it is. 100644 is a plain file: a symbolic link is 120000,
  // an executable 100755, a submodule 160000, and each is refused.
  if (tree?.truncated) refuse('the tree of the head commit is too large to read whole');
  const entries = (tree?.tree ?? []).filter((e) => e.path === f.filename);
  if (entries.length !== 1) refuse('the file is not in the tree of the head commit');
  const e = entries[0];
  if (e.type !== 'blob' || e.mode !== '100644') refuse('the file must be a plain file (not a link, not executable)');
  if (e.sha !== f.sha) refuse('the file list and the tree disagree about the content');
  if (!Number.isInteger(e.size) || e.size < 1 || e.size > MAX_BYTES) refuse(`the file must be between 1 and ${MAX_BYTES} bytes`);
  return { file: f.filename, module: moduleOf(f.filename), head, blob: f.sha, author, size: e.size };
}

// The gap as the desk posts it. Its file must be the file of the pull request.
export function checkGap(gaps, pick, file) {
  const all = Array.isArray(gaps?.gaps) ? gaps.gaps : refuse('the gap list has no gaps');
  const found = all.filter(pick);
  if (found.length !== 1) refuse('the gap is not posted (it may be checked already, or withdrawn)');
  const g = found[0];
  if (typeof g.id !== 'string' || !GAP_RE.test(g.id)) refuse('the posted gap has a malformed id');
  if (g.file !== file || !FILE_RE.test(file)) refuse(`the file of gap ${g.id} is not the file of this pull request`);
  if (g.module !== moduleOf(file)) refuse(`gap ${g.id} names a module that is not its file`);
  if (typeof g.statement !== 'string' || !g.statement.trim() || g.statement.includes('\0')) refuse(`gap ${g.id} has no statement`);
  const imports = g.imports ?? [];
  if (!Array.isArray(imports) || !imports.every((m) => typeof m === 'string' && MODULE_RE.test(m))) refuse(`gap ${g.id} lists a malformed import`);
  return { id: g.id, statement: g.statement, imports };
}

// The import rule. The file starts with its import lines, one module per line, and nothing else
// is among them. Each must be Mathlib, a module of Mathlib, or a module the gap lists. After the
// import lines the word `import` may not appear at all: Lean reads imports through comments, so
// `/- -/ import X` on a later line would still be an import. A plain rule, stricter than Lean.
export function checkImports(bytes, allowed) {
  if (bytes.length > MAX_BYTES) refuse(`the file is larger than ${MAX_BYTES} bytes`);
  let text;
  try { text = new TextDecoder('utf-8', { fatal: true }).decode(bytes); } catch { return refuse('the file is not UTF-8 text'); }
  if (text.includes('\0')) refuse('the file holds a NUL byte');
  const lines = text.split('\n').map((l) => l.replace(/\r$/, ''));
  const ok = typeof allowed === 'function' ? { has: allowed } : new Set(allowed);
  const seen = [];
  let i = 0;
  for (; i < lines.length; i += 1) {
    const l = lines[i];
    if (l.trim() === '') continue;
    const m = /^import ([A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*)[ \t]*$/.exec(l);
    if (!m) break;
    const name = m[1];
    if (!(name === 'Mathlib' || name.startsWith('Mathlib.') || ok.has(name) || (ok.has('PEqualNP.GRH') && name.startsWith('PEqualNP.GRHSource.')))) refuse(`line ${i + 1}: import ${name} is not allowed (only Mathlib and the modules the gap lists)`);
    seen.push(name);
  }
  for (; i < lines.length; i += 1) {
    if (/(^|[^A-Za-z0-9_])import([^A-Za-z0-9_]|$)/.test(lines[i])) refuse(`line ${i + 1}: the word "import" after the import lines (imports are plain lines at the top, one module each)`);
  }
  checkPlain(text);
  return seen;
}

// THE DANGEROUS-BY-NAME RULE: a first filter, NOT what makes an outside file safe to build. A
// Lean file runs code while it compiles; what contains that is the sandbox this job runs in (no
// secrets, no network, a time limit, a machine thrown away after) and the checker's own rules.
// This rule refuses, early and by name, what has no place in a proof file: code that runs at
// build time, new syntax, kernel bypasses, the meta-programming namespaces, string literals.
//   1. The RAW text is searched, comments included, and nothing is stripped: a stripper can be
//      led astray, so none is used. A refused word inside a comment is refused too: reword it.
//   2. It does NOT judge form. Comment prose at column 0, a `#` heading in a doc comment, a small
//      data type (`inductive ... deriving DecidableEq`) or an instance are built and judged by
//      the checker; whether such a file is merged is decided where it is read before any merge.
//      (Measured 2026-11-23: a rule that also refused form bounced nine honest proofs of
//      eighteen, each for a comment line or a small enumerated type.)
//   3. KNOWN LIMIT: the list cannot be complete. What it misses meets the sandbox.
// The only attributes are `@[simp]` and `@[local simp]`; the only options are four limits.
const B = String.raw`(?<![A-Za-z0-9_])`, A = String.raw`(?![A-Za-z0-9_])`;
const FORBIDDEN = new RegExp([
  String.raw`"|[«»]|simproc|builtin_|native|bv_decide|ofReduce|reduceNat|reduceBool`,
  '|' + B + String.raw`(Lean|System|IO|Elab|Meta|Lake|FS|Process|EIO)` + A,
  String.raw`|_root_` + A + String.raw`|RealWorld|BaseIO|include_str|notation|[A-Za-z0-9_]%|polyrith|initialize|run_cmd|run_tac|run_elab|run_meta|by_elab`,
  '|' + B + String.raw`elab|` + B + String.raw`macro|` + B + 'syntax' + A + '|' + B + 'attribute' + A,
  '|' + B + 'axiom' + A + '|' + B + 'opaque' + A + String.raw`|unsafe|` + B + 'partial' + A + String.raw`|sorry|` + B + 'admit' + A,
  String.raw`|#[a-z_][a-z_]{2,}|implemented_by|extern`,
  String.raw`|` + '`' + String.raw`\([a-z]+\||\$\(|%\[|@\[|register_|declare_|lcProof|lcUnreachable|` + B + 'infix|' + B + 'prefix' + A + '|' + B + 'postfix' + A,
  String.raw`|set_option|binder_predicate|unif_hint|^\s*add_\w+|unseal|compile_inductive|irreducible_def`,
].join(''), 'u');
// The four limit options, wherever they stand, are taken out before the list is asked; every
// other set_option, at column 0 or indented, is refused by it.
const LIMIT = /set_option (maxRecDepth|maxHeartbeats|synthInstance\.maxSize|synthInstance\.maxHeartbeats) [0-9]+ in(?![A-Za-z0-9_])/gu;
const INVISIBLE = /[​-‏‪-‮⁠-⁩﻿]/u;
const CONTROL = /[\u0000-\u0008\u000b-\u001f\u007f]/u;

export function checkPlain(text) {
  if (CONTROL.test(text.replace(/\r?\n/g, ''))) refuse('the file holds control characters');
  if (INVISIBLE.test(text)) refuse('the file holds invisible or direction-changing characters');
  let theorems = 0;
  text.split('\n').forEach((raw, k) => {
    const line = raw.replace(/\r$/, '');
    const m = FORBIDDEN.exec(line.replace(LIMIT, '').replace(/@\[(local )?simp\]/gu, ''));
    if (m) refuse(`line ${k + 1}: "${m[0].trim()}" is not allowed in a proof file, in code or in a comment (no code that runs at build time, no new syntax, no string literals, no attributes but simp, no options but the four limits)`);
    if (/^\s*(@\[(local )?simp\] )?((private|protected) )?theorem /u.test(line)) theorems += 1;
  });
  if (theorems === 0) refuse('the file holds no theorem');
}

// WHAT THE BASE STEP MAY BUILD. A gap may list modules that outsiders wrote (anything under
// PEqualNP.Outside, merged on the base branch). A Lean file runs code while it compiles, so such
// a module is never built by the base step: it is built in the locked step, by the checker's own
// build of the judged file, as the account that compiles the judged file. This walks the imports
// of every listed module, as plain text, and splits them:
//   outside: every outside-written module reached (through outside modules only);
//   base:    every other project module reached; the base step builds these.
// Refused: a listed module that is the judged file or is not a plain file of the base tree; an
// outside module whose text fails the rules a proof file must pass (checkImports, checkPlain:
// a second net, the sandbox is the first); a base module that imports an outside module (it
// could be built neither before the locked step, which would compile outside code, nor inside
// it, where nothing of the base may be written); a project module that is not under the
// PEqualNP root (the checker's fixtures are never a gap's import); more than MAX_OUTSIDE
// outside modules (each one is compiled on every run that lists it).
// CONSEQUENCE: a fleet module that imports an outside proof can never be a listed import. A
// file that builds on outside proofs imports the outside modules themselves, and the gap lists
// them; fleet helpers built on outside proofs stay off the lists.
export const OUTSIDE_MODULE_RE = /^(?:PEqualNP\.Outside\.L_[a-z0-9_]+|Conjectures\.[A-Z][A-Za-z0-9]*\.[A-Z][A-Za-z0-9]*)$/;
export const MAX_OUTSIDE = 16;
const PROJECT_RE = /^(PEqualNP|Conjectures|CheckerSuite)(\.[A-Za-z][A-Za-z0-9_]*)*$/;
const BASE_ROOT_RE = /^(?:PEqualNP|Conjectures)(\.[A-Za-z][A-Za-z0-9_]*)*$/;
const isOutside = (m) => ['PEqualNP.Outside', 'Conjectures'].some(root => m === root || m.startsWith(root + '.'));

// The import lines of a base module, read the way Lean reads a header: comments, `module`,
// `prelude` and the modifiers `public`, `meta`, `private`, `all` are passed over. Base files are
// the project's own and are not hostile; the reader still fails closed: an `import` at the start
// of a line below the header it found is refused, never passed over.
export function headerImports(text, name) {
  const toks = [];
  let i = 0, line = 0;
  while (i < text.length) {
    const c = text[i];
    if (c === '\n') { line += 1; i += 1; } else if (/\s/.test(c)) { i += 1; }
    else if (text.startsWith('--', i)) { while (i < text.length && text[i] !== '\n') i += 1; }
    else if (text.startsWith('/-', i)) {
      let depth = 0;
      do {
        if (text.startsWith('/-', i)) { depth += 1; i += 2; } else if (text.startsWith('-/', i)) { depth -= 1; i += 2; }
        else { if (text[i] === '\n') line += 1; i += 1; }
      } while (depth > 0 && i < text.length);
    } else {
      let j = i; while (j < text.length && !/\s/.test(text[j]) && !text.startsWith('--', j) && !text.startsWith('/-', j)) j += 1;
      toks.push({ t: text.slice(i, j), line }); i = j;
    }
  }
  const out = [];
  let k = 0, end = 0;
  for (; k < toks.length; k += 1) {
    const t = toks[k].t;
    if (['module', 'prelude', 'public', 'meta', 'private'].includes(t)) continue;
    if (t !== 'import') break;
    k += 1;
    if (toks[k]?.t === 'all') k += 1;
    const id = (toks[k]?.t ?? '').replace(/[«»]/g, '');
    if (!/^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$/.test(id)) refuse(`cannot read the imports of ${name}`);
    out.push(id); end = toks[k].line;
  }
  const lines = text.split('\n');
  for (let n = end + 1; n < lines.length; n += 1) {
    if (/^\s*((public|meta|private)\s+)*import\s/.test(lines[n])) refuse(`cannot read the imports of ${name}: an import line below its header (line ${n + 1})`);
  }
  return out;
}

export function importClosure(listed, read, judged, buildOrder = [], limit = MAX_OUTSIDE) {
  const outside = new Set(), base = new Set();
  const visit = (m, from) => {
    if (outside.has(m) || base.has(m)) return;
    if (!BASE_ROOT_RE.test(m)) refuse(`${from ? `${from} imports` : 'the gap lists'} ${m}, which is not under an allowed project root`);
    if (m === judged) refuse(`${from ? `${from} imports` : 'the gap lists'} ${m}, the file being judged`);
    const bytes = read(m);
    if (bytes === null) refuse(`${from ? `${from} imports` : 'the gap lists'} ${m}, which is not a plain file of the base tree`);
    if (isOutside(m)) {
      if (!OUTSIDE_MODULE_RE.test(m)) refuse(`${m} is not the name of an outside proof file`);
      outside.add(m);
      if (outside.size > limit) refuse(`more than ${limit} outside modules are listed or reached (${[...outside].slice(0, 3).join(', ')}, ...); list fewer`);
      // The same rules a proof file passes before it is built, on the text as it is on the base.
      let imports;
      try { imports = checkImports(bytes, (x) => PROJECT_RE.test(x)); } catch (e) { if (e instanceof Refused) refuse(`the listed outside module ${m}: ${e.message}`); throw e; }
      for (const x of imports) if (PROJECT_RE.test(x)) visit(x, m);
      buildOrder.push(m);
    } else {
      base.add(m);
      for (const x of headerImports(new TextDecoder().decode(bytes), m)) {
        if (!PROJECT_RE.test(x)) continue;
        if (isOutside(x)) refuse(`the base module ${m} imports the outside-written ${x}; it can be built neither before the locked step nor in it`);
        visit(x, m);
      }
    }
  };
  for (const m of listed) visit(m, null);
  return { outside: [...outside].sort(), base: [...base].sort() };
}

const put = (dir, name, value) => writeFileSync(join(dir, name), value);
const main = () => {
  const [cmd, ...a] = process.argv.slice(2);
  if (cmd === 'pr' && a.length === 6) {
    const r = checkPr(json(a[0]), json(a[1]), json(a[2]), a[3], a[4]);
    for (const [k, v] of Object.entries(r)) put(a[5], `pr.${k}`, `${v}\n`);
  } else if ((cmd === 'gap' && a.length === 4) || (cmd === 'gap-of-file' && a.length === 3)) {
    const byId = cmd === 'gap';
    const [gapsPath, file, out] = byId ? [a[0], a[2], a[3]] : a;
    if (byId && !GAP_RE.test(a[1])) refuse('the gap id is malformed');
    const g = checkGap(json(gapsPath), byId ? (x) => x?.id === a[1] : (x) => x?.file === file, file);
    put(out, 'gap.id', `${g.id}\n`);
    put(out, 'statement.txt', g.statement);          // the posted text, byte for byte
    put(out, 'imports.json', JSON.stringify(g.imports));
    put(out, 'imports.txt', g.imports.map((m) => `${m}\n`).join(''));
  } else if (cmd === 'imports' && (a.length === 2 || a.length === 3)) {
    const listed = json(a[1]);
    const seen = checkImports(readFileSync(a[0]), listed);
    if (a[2]) writeFileSync(a[2], JSON.stringify([...new Set([...listed, ...seen.filter((m) => MODULE_RE.test(m))])]));
    process.stdout.write(`imports allowed: ${seen.join(' ') || '(none)'}\n`);
  } else if ((cmd === 'closure' || cmd === 'assembly-closure') && a.length === 4) {
    const [baseDir, importsPath, judgedFile, out] = a;
    if (!FILE_RE.test(judgedFile)) refuse('the judged file is not a registered community proof path');
    const listed = json(importsPath);
    if (!Array.isArray(listed) || !listed.every((m) => typeof m === 'string' && MODULE_RE.test(m))) refuse('the listed imports are malformed');
    // A module's file in the base tree: a plain file (not a link), at most 2 MiB, else null.
    const read = (m) => {
      const p = join(baseDir, 'lean', ...m.split('.')) + '.lean';
      let st; try { st = lstatSync(p); } catch { return null; }
      if (!st.isFile() || st.size > MAX_BYTES) return null;
      return readFileSync(p);
    };
    const buildOrder = [];
    const r = importClosure(listed, read, moduleOf(judgedFile), buildOrder,
      cmd === 'assembly-closure' ? (MAX_OUTSIDE + 1) * listed.length : MAX_OUTSIDE);
    put(out, 'outside-build-order.txt', buildOrder.map((m) => `${m}\n`).join(''));
    put(out, 'base-imports.txt', r.base.map((m) => `${m}\n`).join(''));
    put(out, 'outside-imports.txt', r.outside.map((m) => `${m}\n`).join(''));
    put(out, 'outside-sources.txt', r.outside.map((m) => `base/lean/${m.split('.').join('/')}.lean\n`).join(''));
    process.stdout.write(`built before the locked step: ${r.base.join(' ') || '(none)'}\noutside-written, built only in the locked step: ${r.outside.join(' ') || '(none)'}\n`);
  } else {
    process.stderr.write('usage: outside-guard.mjs pr|gap|gap-of-file|imports|closure ... (see the header)\n');
    process.exit(3);
  }
};

if (process.argv[1] && import.meta.url === new URL(`file://${process.argv[1]}`).href) {
  try { main(); } catch (e) {
    if (!(e instanceof Refused)) throw e;
    process.stdout.write(`REFUSED: ${e.message}\n`);
    process.exit(1);
  }
}
