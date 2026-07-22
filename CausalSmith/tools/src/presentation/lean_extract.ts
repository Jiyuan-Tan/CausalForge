/**
 * Statement-source extraction for the website drawer.
 * Theorems/lemmas: from the decl keyword line (plus preceding doc comment) up
 * to the first `:=`. Defs/structures: full source capped at 40 lines.
 */

const DECL_RE = (decl: string) =>
  new RegExp(
    // Modifiers (private/protected/noncomputable/scoped) are a repeatable prefix —
    // NOT just `noncomputable def`, so `noncomputable abbrev`/`noncomputable
    // structure` (e.g. the `p10_triangularClass` alias) also match.
    `^\\s*(?:@\\[[^\\]]*\\]\\s*)?(?:(?:private|protected|noncomputable|scoped|unsafe)\\s+)*(theorem|lemma|def|abbrev|structure|class)\\s+${decl.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b`,
  );

const DECL_LINE_RE =
  /^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|scoped|unsafe)\s+)*(def|abbrev|structure|class|theorem|lemma)\s+([A-Za-z_][\w'.]*)/;

const TOP_LEVEL_BOUNDARY_RE =
  /^\s*(?:@\[|(?:(?:private|protected|noncomputable|scoped|unsafe)\s+)*(?:def|abbrev|structure|class|theorem|lemma|instance|inductive|coinductive|opaque|axiom|example|macro|syntax|notation)\b|(?:namespace|section|end|open|export|attribute|variable|include|omit|local|set_option)\b)/;

interface LeanLexState { blockDepth: number; inString: boolean; escaped: boolean }

/** Replace comments/string contents with spaces while preserving indentation. */
function visibleLeanCode(line: string, state: LeanLexState): string {
  let out = "";
  for (let i = 0; i < line.length; i++) {
    const c = line[i];
    const n = line[i + 1];
    if (state.blockDepth > 0) {
      if (c === "/" && n === "-") { state.blockDepth++; out += "  "; i++; }
      else if (c === "-" && n === "/") { state.blockDepth--; out += "  "; i++; }
      else out += " ";
      continue;
    }
    if (state.inString) {
      out += " ";
      if (state.escaped) state.escaped = false;
      else if (c === "\\") state.escaped = true;
      else if (c === '"') state.inString = false;
      continue;
    }
    if (c === "-" && n === "-") {
      return out + " ".repeat(line.length - i);
    }
    if (c === "/" && n === "-") { state.blockDepth++; out += "  "; i++; continue; }
    if (c === '"') { state.inString = true; out += " "; continue; }
    out += c;
  }
  // Ordinary Lean strings do not continue across physical lines.
  if (state.inString && !state.escaped) state.inString = false;
  state.escaped = false;
  return out;
}

function findDeclStart(lines: string[], decl: string, line: number): number {
  const leaf = decl.includes(".") ? decl.slice(decl.lastIndexOf(".") + 1) : decl;
  for (const cand of leaf === decl ? [decl] : [decl, leaf]) {
    const re = DECL_RE(cand);
    const probe = (i: number) => i >= 0 && i < lines.length && re.test(lines[i]);
    for (let d = 0; d <= 40; d++) {
      if (probe(line - 1 + d)) return line - 1 + d;
      if (probe(line - 1 - d)) return line - 1 - d;
    }
    const start = lines.findIndex((l) => re.test(l));
    if (start >= 0) return start;
  }
  throw new Error(`declaration ${decl} not found`);
}

/** Pop a declaration snippet's trailing preamble that actually belongs to the NEXT declaration:
 *  blank lines, `--`/`-- @node:` line comments, and whole `/-- … -/` block comments (multi-line
 *  included — their interior lines don't individually look like a comment). Stops at the first
 *  genuine body line of this decl. Mutates `out` in place. */
function stripTrailingPreamble(out: string[]): void {
  for (;;) {
    const k = out.length - 1;
    if (k < 0) break;
    const last = out[k];
    if (last.trim() === "" || /^\s*--/.test(last)) {
      out.pop();
      continue;
    }
    if (/-\/\s*$/.test(last)) {
      // line closes a block comment — drop the whole block back to (and including) its opener
      let j = k;
      while (j > 0 && !/^\s*\/-/.test(out[j])) j--;
      if (!/^\s*\/-/.test(out[j])) break; // no opener — leave as-is rather than over-pop
      out.length = j;
      continue;
    }
    break; // genuine body line of THIS declaration
  }
}

/** `line` is a 1-indexed hint (crosswalk line); search ±40 lines around it, then the whole file. */
export function extractDeclSnippet(source: string, decl: string, line: number): string {
  const lines = source.split("\n");
  // A crosswalk row records the Lean name as a fully-qualified path
  // (`Ns.Sub.FeasibleDesign`), but the source declares only the LEAF (`structure
  // FeasibleDesign`). Try the full name first, then fall back to the leaf — the by-leaf
  // resolution the caller relies on. Both are anchored `^…keyword <name>\b`, so a leaf never
  // matches an unrelated longer identifier.
  const start = findDeclStart(lines, decl, line);
  // Include the declaration's OWN preceding doc-comment — whole `/-- … -/` blocks, not just
  // the last line. A multi-line docstring's interior lines don't individually look like a
  // comment, so the old line-by-line test started the snippet mid-sentence. Consume contiguous
  // blank/`--` lines and AT MOST ONE block comment above the keyword; STOP at a `-- @node:`
  // pipeline tag (it is metadata, not the statement) so it never appears, and never cross into
  // the previous declaration.
  let s = start;
  let consumedBlock = false;
  for (;;) {
    if (s === 0) break;
    const above = lines[s - 1];
    if (/^\s*--\s*@node:/.test(above)) break; // pipeline tag — exclude it and stop
    if (above.trim() === "" || /^\s*--/.test(above)) { s--; continue; }
    if (!consumedBlock && /-\/\s*$/.test(above)) {
      let j = s - 1;
      while (j > 0 && !/^\s*\/-/.test(lines[j])) j--;
      if (!/^\s*\/-/.test(lines[j])) break; // no opener found — don't run away upward
      s = j;
      consumedBlock = true;
      continue;
    }
    break;
  }
  if (start - s > 24) s = start; // pathological docstring: show the decl alone, not a wall of doc
  while (s < start && lines[s].trim() === "") s++; // drop any leading blank lines
  const isProp = /^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma)\b/.test(
    lines[start],
  );
  const out: string[] = [];
  // Theorem statements must NEVER be silently cut — the conclusion is the point.
  // Scan to the `:=` however long the hypothesis ledger is (hard cap only as a
  // pathology guard, with an explicit marker).
  const cap = isProp ? 400 : 120;
  let truncated = true;
  // A theorem's terminating `:=` sits at bracket depth 0; `:=` inside binder
  // parentheses (e.g. `let lam := …` in a hypothesis type) must not cut.
  let depth = 0;
  // Block-comment nesting depth while scanning a def/structure body. The "next declaration" probe
  // must NOT fire on a decl keyword that is really PROSE inside a `/- … -/` docstring — the
  // `upperRisk` docstring says "…the policy class Π…", and a line starting with "class"/"def"/"end"
  // there used to truncate the snippet mid-docstring, leaking the next decl's `@node:` + doc-comment.
  let blockDepth = 0;
  const advanceBlockDepth = (line: string) => {
    for (let j = 0; j < line.length - 1; j++) {
      if (line[j] === "/" && line[j + 1] === "-") { blockDepth++; j++; }
      else if (line[j] === "-" && line[j + 1] === "/") { blockDepth = Math.max(0, blockDepth - 1); j++; }
    }
  };
  for (let i = s; i < Math.min(lines.length, start + cap); i++) {
    const l = lines[i];
    if (isProp) {
      const scan = l.replace(/--.*$/, ""); // line comments can't move depth or cut
      let cut = -1;
      for (let j = 0; j < scan.length; j++) {
        const c = scan[j];
        if (c === "(" || c === "[" || c === "{" || c === "⟨" || c === "⦃") depth++;
        else if (c === ")" || c === "]" || c === "}" || c === "⟩" || c === "⦄") depth--;
        else if (c === ":" && scan[j + 1] === "=" && depth === 0) {
          cut = j;
          break;
        }
      }
      if (cut >= 0) {
        const head = l.slice(0, cut).trimEnd();
        if (head !== "") out.push(head);
        truncated = false;
        break;
      }
      out.push(l);
    } else {
      if (blockDepth === 0 && i > start && (DECL_LINE_RE.test(l) || /^\s*(?:end\b|@\[)/.test(l))) {
        // why: next-decl boundaries must catch modifiers/indentation such as `noncomputable abbrev`.
        // The NEXT declaration's leading preamble (blank lines, its `-- @node:` tag, and its
        // `/-- … -/` doc-comment) was already pushed — it sits ABOVE the next keyword. Drop it,
        // including MULTI-LINE doc-comments whose interior lines don't look like comments, so the
        // snippet ends at THIS decl's body, not a dangling next-decl `-- @node:` + docstring.
        stripTrailingPreamble(out);
        truncated = false;
        break;
      }
      out.push(l);
      advanceBlockDepth(l); // track `/- … -/` nesting so a "class"/"def" word in a docstring is prose
    }
    if (i === lines.length - 1) truncated = false;
  }
  if (truncated) out.push("  -- … (truncated; see the full file via the GitHub link)");
  return out.join("\n").trimEnd();
}

/**
 * Extract the complete source of one top-level declaration, including its proof/body.
 * This is intentionally separate from `extractDeclSnippet`, whose website-facing
 * contract stops theorem/lemma text before `:=`. Presentation proof caches and audits
 * must invalidate on edits to the actual proof without invalidating on unrelated
 * declarations elsewhere in the same Lean file.
 */
export function extractFullDeclSource(source: string, decl: string, line: number): string {
  const lines = source.split("\n");
  const start = findDeclStart(lines, decl, line);
  const indent = lines[start].match(/^\s*/)?.[0].length ?? 0;
  const lex: LeanLexState = { blockDepth: 0, inString: false, escaped: false };
  visibleLeanCode(lines[start], lex); // initialize comments opened on the declaration line
  let end = lines.length;
  for (let i = start + 1; i < lines.length; i++) {
    const raw = lines[i];
    const leading = raw.match(/^\s*/)?.[0].length ?? 0;
    const visible = visibleLeanCode(raw, lex);
    if (
      leading <= indent &&
      TOP_LEVEL_BOUNDARY_RE.test(visible)
    ) {
      end = i;
      break;
    }
  }
  const out = lines.slice(start, end);
  stripTrailingPreamble(out);
  return out.join("\n").trimEnd();
}

/** Non-throwing `extractDeclSnippet`: returns `null` when the decl cannot be located in
 *  `source` (e.g. it was promoted to another package and only `export`ed here, or moved).
 *  Use in the web-bundle emit, where one unresolvable decl must degrade to a placeholder
 *  rather than abort the whole bundle — proof rendering keeps the throwing form (fail loud). */
export function tryExtractDeclSnippet(source: string, decl: string, line: number): string | null {
  try {
    return extractDeclSnippet(source, decl, line);
  } catch {
    return null;
  }
}

/**
 * Lists the top-level declarations in a Lean source (short names as written,
 * which is what the crosswalk / component specs use). Used to widen the
 * composite-component candidate pool to every decl in a paper's modules, so a
 * multi-part definition can reference any of its Lean pieces without each piece
 * being a separate crosswalk entry.
 */
export function parseSourceDecls(source: string): { name: string; line: number; kind: string }[] {
  const out: { name: string; line: number; kind: string }[] = [];
  const lines = source.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const m = DECL_LINE_RE.exec(lines[i]);
    if (m) out.push({ name: m[2], line: i + 1, kind: m[1] });
  }
  return out;
}

/**
 * Slices named hypothesis binders out of an extracted theorem statement: for
 * each binder name, the parenthesized group `(name : …)` (balanced) plus any
 * `--` comment lines directly above it. Used to show the Lean content of
 * composite paper objects whose formalization lives in theorem hypotheses.
 */
export function extractHypothesisBinders(statement: string, binders: string[]): string {
  const out: string[] = [];
  for (const name of binders) {
    const re = new RegExp(`\\(\\s*${name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\s*:`);
    const m = re.exec(statement);
    if (!m) {
      out.push(`-- (binder ${name} not found in the statement)`);
      continue;
    }
    // balanced-paren scan from the opening parenthesis
    let depth = 0;
    let end = m.index;
    for (let i = m.index; i < statement.length; i++) {
      if (statement[i] === "(") depth++;
      else if (statement[i] === ")") {
        depth--;
        if (depth === 0) {
          end = i + 1;
          break;
        }
      }
    }
    // contiguous comment lines directly above the binder's line
    const upto = statement.slice(0, m.index);
    const lineStart = upto.lastIndexOf("\n") + 1;
    const prevLines = upto.slice(0, lineStart).split("\n");
    const comments: string[] = [];
    for (let i = prevLines.length - 1; i >= 0; i--) {
      if (/^\s*--/.test(prevLines[i])) comments.unshift(prevLines[i]);
      else break;
    }
    out.push(...comments, statement.slice(m.index, end).trim());
  }
  return out.join("\n");
}

/**
 * Comment-stripped sorry scan for the badge gate. Block/doc comments must be
 * stripped too: module docstrings narrate pipeline history ("sorry-only
 * scaffold") and tripped the scan. Lean block comments nest; non-greedy
 * removal can only over-report sorry (a stranded `-/` tail), never claim
 * sorry-free when a code-level sorry exists.
 */
export function sorryFree(source: string): boolean {
  const stripped = source.replace(/\/-[\s\S]*?-\//g, "").replace(/--.*$/gm, "");
  return !/\bsorry\b/.test(stripped);
}
