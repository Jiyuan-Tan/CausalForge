// Reactive Lean-file splitter (causalsmith Mechanism 3).
//
// Splits a single oversized, FLAT-namespace Lean file (one `namespace … end`,
// no nested `section`/mid-file `variable`/`open`) into size-bounded sibling
// part files.  Relies on the fact that a Lean file is already in dependency
// order (no forward refs): consecutive chunks + a linear import chain (Part_i
// imports Part_{i-1}) preserve every reference.  Cross-part `private` decls are
// de-privatized so later parts (and the original) can see them.
//
// Two modes for the ORIGINAL file:
//  * default — it becomes a thin re-export aggregator (imports all parts), so
//    downstream `import`s never change;
//  * PINNED-SUFFIX (`opts.pinnedDecls`, for T-block theorem files) — only the
//    dependency-safe PREFIX before the first pinned decl is extracted; the
//    original RETAINS the pinned `theorem`(s) + its preamble and imports the
//    parts, so tooling that locates a banked theorem BY FILE still finds it.
//
// REFUSES (returns {ok:false}) any file that is not flat-namespace — it never
// silently mangles a file with nested sections or local variable scopes.
// Caller is expected to `lake build` and roll back on failure (verify-or-rollback).

const DECL_RE =
  /^(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+|unsafe\s+|partial\s+)*(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)\b/;

/** Block-comment nesting depth at the START of each line (Lean `/- -/` nest;
 *  `/--`,`/-!` are block comments too).  `--` is a line comment.  Minimal string
 *  handling so a `"…/-…"` literal does not open a comment. */
export function commentDepthAtLineStart(lines: string[]): number[] {
  const depths: number[] = [];
  let depth = 0;
  for (const line of lines) {
    depths.push(depth);
    let i = 0;
    let inStr = false;
    while (i < line.length) {
      const two = line.slice(i, i + 2);
      if (depth > 0) {
        if (two === '-/') { depth--; i += 2; continue; }
        if (two === '/-') { depth++; i += 2; continue; }
        i++; continue;
      }
      // depth === 0
      if (inStr) {
        if (line[i] === '\\') { i += 2; continue; }
        if (line[i] === '"') { inStr = false; i++; continue; }
        i++; continue;
      }
      if (two === '--') break; // line comment: rest of line irrelevant to depth
      if (two === '/-') { depth++; i += 2; continue; }
      if (line[i] === '"') { inStr = true; i++; continue; }
      i++;
    }
  }
  return depths;
}

const isBlankLine = (s: string) => s.trim() === '';
const opensComment = (s: string) => { const t = s.trimStart(); return t.startsWith('/-'); };
const isLineComment = (s: string) => s.trimStart().startsWith('--');
const isAttr = (s: string) => s.trimStart().startsWith('@[');
/**
 * A `<command> … in` prefix, which applies to the NEXT command and therefore belongs to the
 * following declaration's header. Splitting between the two detaches the prefix: the decl loses
 * (e.g.) its heartbeat budget and the prefix lands on an unrelated command.
 */
const isCommandPrefix = (s: string) =>
  /^(?:set_option|attribute|open|local|scoped|omit|suppress_compilation|macro_rules|binder_predicate)\b.*\bin\s*$/
    .test(s.trimStart());

export interface SplitOptions {
  /** Soft max lines per part; a single decl is never split even if it exceeds this. */
  lineBudget?: number;
  /** Module path prefix, e.g. `CausalSmith.Stat.STAT_AteOverlapDecay_Research`. */
  modulePrefix: string;
  /** Base name of the file being split, e.g. `Helpers`. */
  baseName: string;
  /**
   * PINNED-SUFFIX mode (for T-block theorem files): names of declarations that
   * MUST stay in the original file — the banked `theorem`s, which downstream
   * tooling (`reconcileStage3Outcomes`) and the catalogue locate BY FILE. When
   * set and present, only the dependency-safe PREFIX of decls strictly BEFORE
   * the first pinned decl is extracted into `_Part<n>` siblings; the original
   * retains everything from the first pinned decl onward (the theorem + its
   * preamble) and `import`s the sibling parts. A prefix can never reference a
   * suffix decl (files are in dependency order), so extraction is always sound.
   * Empty / absent ⇒ classic whole-file aggregator split.
   */
  pinnedDecls?: Set<string>;
}

export interface SplitPart { moduleName: string; relFileName: string; content: string; lineCount: number; }
export interface SplitResult {
  ok: boolean;
  reason?: string;
  parts: SplitPart[];
  /** New content for the original file (the thin re-export aggregator). */
  aggregator: string;
  declCount: number;
  deprivatized: string[];
}

export function splitFlatNamespaceFile(text: string, opts: SplitOptions): SplitResult {
  const budget = opts.lineBudget ?? 700;
  const lines = text.split('\n');
  const depth = commentDepthAtLineStart(lines);
  const fail = (reason: string): SplitResult =>
    ({ ok: false, reason, parts: [], aggregator: text, declCount: 0, deprivatized: [] });

  // ---- Parse top-level structure (only outside comments). ----
  const nsStarts: number[] = [], nsEnds: number[] = [];
  const badScopes: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    if (depth[i] > 0) continue;
    const t = lines[i].trimStart();
    if (/^namespace\b/.test(t)) nsStarts.push(i);
    else if (/^end\b/.test(t) && t.trim() !== 'end') nsEnds.push(i);
    // `noncomputable section` opens a scope exactly like `section`; matching only /^section\b/
    // let it through, and because the anonymous `end` closing it is excluded from the `end` count
    // below, such a file passed the "exactly one namespace…end" check and was split into parts
    // that neither reproduce nor close the scope.
    else if (/^(?:noncomputable\s+)?section\b/.test(t) || /^variable\b/.test(t) || (/^open\b/.test(t) && !isCommandPrefix(t))) {
      // `open`/`variable` are allowed only in the preamble (before first decl);
      // a `section` anywhere makes scoping non-flat — flag for the post-preamble check.
      badScopes.push(`${i + 1}:${t.slice(0, 30)}`);
    }
  }
  if (nsStarts.length !== 1 || nsEnds.length !== 1)
    return fail(`expected exactly one namespace…end (found ${nsStarts.length} namespace / ${nsEnds.length} end)`);
  const nsLine = nsStarts[0], endLine = nsEnds[0];
  const namespaceName = lines[nsLine].trim().replace(/^namespace\s+/, '').trim();

  // ---- Decl keyword lines (outside comments). ----
  const declLines: number[] = [];
  for (let i = nsLine + 1; i < endLine; i++) {
    if (depth[i] > 0) continue;
    if (DECL_RE.test(lines[i])) declLines.push(i);
  }
  if (declLines.length < 2) return fail(`too few decls to split (${declLines.length})`);

  // ---- Header start (absorb the contiguous docstring/attr block directly above). ----
  const headerStart = (declLine: number): number => {
    let h = declLine;
    while (h - 1 > nsLine) {
      const p = h - 1;
      // A line strictly inside a block comment (depth>0) is part of the docstring
      // even when visually blank — absorb it (do NOT treat as a separator).
      const insideComment = depth[p] > 0;
      const startsComment = opensComment(lines[p]); // depth 0 but opens `/-`,`/--`,`/-!`
      // A `<command> … in` prefix binds to the decl below it, so it is part of this header.
      if (insideComment || startsComment || isLineComment(lines[p]) || isAttr(lines[p])
          || isCommandPrefix(lines[p])) { h = p; continue; }
      // Not a comment/attr line: a true (depth-0) blank is the separator → stop;
      // code also stops the walk.
      break;
    }
    return h;
  };
  const headers = declLines.map(headerStart);

  // Every `<command> … in` prefix must sit inside some decl's absorbed header. One that does not
  // (e.g. separated from its decl by a blank line, or trailing the last decl) would be detached
  // by a chunk boundary, so refuse the split rather than guess where it belongs.
  for (let i = nsLine + 1; i < endLine; i++) {
    if (depth[i] > 0 || !isCommandPrefix(lines[i])) continue;
    const covered = declLines.some((d, k) => headers[k] <= i && i < d);
    if (!covered)
      return fail(`command prefix at ${i + 1}:${lines[i].trim().slice(0, 40)} is not attached to a following decl`);
  }

  // Reject anything between namespace and first decl that is a `section` (non-flat),
  // or any `open`/`variable`/`section` that appears AFTER the first decl header.
  const firstHeader = headers[0];
  for (const s of badScopes) {
    const ln = parseInt(s, 10) - 1;
    if (s.includes('section')) return fail(`non-flat: 'section' at ${s}`);
    if (ln >= firstHeader) return fail(`non-flat: open/variable after first decl at ${s}`);
  }

  // ---- Preamble (everything before the first decl header) + namespace name. ----
  const preambleLines = lines.slice(0, firstHeader);
  const importInsertIdx = (() => {
    let last = -1;
    for (let i = 0; i < preambleLines.length; i++)
      if (depth[i] === 0 && /^import\b/.test(preambleLines[i].trimStart())) last = i;
    return last;
  })();
  if (importInsertIdx < 0) return fail('no import line found in preamble');

  // ---- Decl name extraction (for de-privatization). ----
  const declName = (declLine: number): { name: string; isPrivate: boolean } => {
    const m = lines[declLine].match(
      /^((?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+|unsafe\s+|partial\s+)*)(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)\s+([^\s({:[]+)/);
    return { name: m ? m[2] : '', isPrivate: /(^|\s)private\s/.test(lines[declLine].slice(0, (lines[declLine].match(DECL_RE)?.[0].length ?? 0))) };
  };
  const declMeta = declLines.map(declName);

  // ---- PINNED-SUFFIX: extract only the decls strictly BEFORE the first pinned
  // (banked-theorem) decl; the original retains everything from there on. Empty
  // pin set ⇒ extractCount = all decls (classic whole-file aggregator split). ----
  const pinned = opts.pinnedDecls;
  let extractCount = declLines.length;
  let pinMode = false;
  if (pinned && pinned.size > 0) {
    const pinIdx = declMeta.findIndex((m) => pinned.has(m.name));
    if (pinIdx < 0)
      return fail(`pinned decl(s) ${[...pinned].join(', ')} not found in file`);
    if (pinIdx === 0)
      return fail(`first decl '${declMeta[0].name}' is pinned — no prefix to extract without moving a banked theorem`);
    extractCount = pinIdx;
    pinMode = true;
  }
  // Line where the retained suffix begins (= EOF/`end` in aggregator mode).
  const suffixStart = extractCount < declLines.length ? headers[extractCount] : endLine;

  // ---- Chunk the extracted prefix decls by line budget (never split a decl). ----
  const chunks: { from: number; to: number; firstDecl: number; lastDecl: number }[] = [];
  let chunkStartIdx = 0;
  for (let d = 0; d < extractCount; d++) {
    const chunkFrom = headers[chunkStartIdx];
    const declEnd = (d + 1 < extractCount ? headers[d + 1] : suffixStart) - 1;
    const linesSoFar = declEnd - chunkFrom + 1;
    const isLast = d === extractCount - 1;
    if (linesSoFar > budget && d > chunkStartIdx) {
      // close chunk at previous decl
      const prevEnd = headers[d] - 1;
      chunks.push({ from: headers[chunkStartIdx], to: prevEnd, firstDecl: chunkStartIdx, lastDecl: d - 1 });
      chunkStartIdx = d;
    }
    if (isLast) {
      chunks.push({ from: headers[chunkStartIdx], to: suffixStart - 1, firstDecl: chunkStartIdx, lastDecl: d });
    }
  }
  // Aggregator mode needs ≥2 chunks to be worth it; pinned mode extracts a
  // prefix off the theorem file, so even ONE extracted chunk is a real win.
  if (chunks.length < (pinMode ? 1 : 2))
    return fail(`budget ${budget} yields nothing to extract`);

  // Comment-balance guard: a chunk must begin and end OUTSIDE any block comment,
  // else the boundary split a docstring (depth[to+1] is the depth entering the
  // line after the chunk's last line).
  for (const c of chunks) {
    const endDepth = c.to + 1 < depth.length ? depth[c.to + 1] : 0;
    if (depth[c.from] !== 0 || endDepth !== 0)
      return fail(`chunk [${c.from + 1}..${c.to + 1}] is not comment-balanced (start depth ${depth[c.from]}, end depth ${endDepth}) — boundary split a comment`);
  }

  // ---- De-privatization: a private PREFIX decl referenced (as a token) in a
  // LATER prefix chunk OR in the RETAINED SUFFIX (the theorem that consumes it)
  // must be made visible. ----
  const deprivatized: string[] = [];
  const chunkText = chunks.map(c => lines.slice(c.from, c.to + 1).join('\n'));
  // Everything kept in the original from the first pinned decl onward (empty in
  // aggregator mode, where suffixStart === endLine).
  const suffixText = lines.slice(suffixStart, endLine).join('\n');
  const toDeprivatize = new Set<number>(); // decl index
  for (let di = 0; di < extractCount; di++) {
    const { name, isPrivate } = declMeta[di];
    if (!isPrivate || !name) continue;
    // which chunk owns decl di?
    const owner = chunks.findIndex(c => di >= c.firstDecl && di <= c.lastDecl);
    const esc = (s: string) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    // full-name reference, e.g. `IsBigOp.mono_rate`
    const reFull = new RegExp(`(^|[^\\w.])${esc(name)}([^\\w]|$)`);
    // dot-notation reference of the last component, e.g. `h.mono_rate` → IsBigOp.mono_rate
    const lastComp = name.includes('.') ? name.slice(name.lastIndexOf('.') + 1) : '';
    const reDot = lastComp ? new RegExp(`\\.${esc(lastComp)}([^\\w]|$)`) : null;
    const refdIn = (txt: string) => reFull.test(txt) || (reDot ? reDot.test(txt) : false);
    let used = refdIn(suffixText);
    for (let cj = owner + 1; !used && cj < chunks.length; cj++) used = refdIn(chunkText[cj]);
    if (used) { toDeprivatize.add(di); deprivatized.push(name); }
  }

  // ---- Build part files. ----
  const partFor = (n: number) => `${opts.baseName}_Part${n}`;
  const parts: SplitPart[] = chunks.map((c, ci) => {
    const partNo = ci + 1;
    const body: string[] = lines.slice(c.from, c.to + 1).slice();
    // de-privatize within this chunk (offset of each decl line into the chunk)
    for (let di = c.firstDecl; di <= c.lastDecl; di++) {
      if (!toDeprivatize.has(di)) continue;
      const off = declLines[di] - c.from;
      if (off >= 0 && off < body.length) body[off] = body[off].replace(/(^\s*)private\s+/, '$1');
    }
    const pre = preambleLines.slice();
    const extraImports: string[] = [];
    for (let k = 1; k < partNo; k++) extraImports.push(`import ${opts.modulePrefix}.${partFor(k)}`);
    // insert earlier-part imports right after the last existing import
    const head = pre.slice(0, importInsertIdx + 1);
    const tail = pre.slice(importInsertIdx + 1);
    const content =
      [...head, ...extraImports, ...tail].join('\n').replace(/\n*$/, '\n') +
      body.join('\n').replace(/\n*$/, '\n') +
      `\nend ${namespaceName}\n`;
    return {
      moduleName: `${opts.modulePrefix}.${partFor(partNo)}`,
      relFileName: `${partFor(partNo)}.lean`,
      content,
      lineCount: content.split('\n').length,
    };
  });

  // ---- New content for the ORIGINAL file. ----
  let aggregator: string;
  if (pinMode) {
    // Retainer: full preamble (license + imports + `namespace`/`open`/`variable`)
    // with the extracted parts imported after the last existing import, then the
    // RETAINED SUFFIX decls (the banked theorem + anything after it) verbatim, then
    // `end`. The theorem stays in its named file; its support lemmas are imported.
    const head = preambleLines.slice(0, importInsertIdx + 1);
    const tailPre = preambleLines.slice(importInsertIdx + 1);
    const partImports = parts.map(p => `import ${p.moduleName}`);
    const retained = lines.slice(suffixStart, endLine); // decls from first pinned to last (no `end`)
    aggregator =
      [...head, ...partImports, ...tailPre].join('\n').replace(/\n*$/, '\n') +
      retained.join('\n').replace(/\n*$/, '\n') +
      `\nend ${namespaceName}\n`;
  } else {
    // Aggregator: license header (leading comment block) + imports of all parts.
    const leadingComment: string[] = [];
    for (let i = 0; i < lines.length; i++) {
      if (depth[i] > 0 || opensComment(lines[i]) || isBlankLine(lines[i]) || isLineComment(lines[i])) leadingComment.push(lines[i]);
      else break;
    }
    const baseImport = preambleLines[importInsertIdx]; // `import …Basic`
    aggregator =
      leadingComment.join('\n').replace(/\n*$/, '\n\n') +
      [baseImport, ...parts.map(p => `import ${p.moduleName}`)].join('\n') + '\n';
  }

  return { ok: true, parts, aggregator, declCount: declLines.length, deprivatized };
}
