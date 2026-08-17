/**
 * NL ↔ Lean crosslink markup, authored in a Lean docstring's FIRST paragraph
 * (the NL translation — docstring-canonical, no side-channel data):
 *
 *   [phrase](hyp:name[,name…])  links the phrase to the statement binder(s)
 *                               with those names;
 *   [phrase](goal)              links the phrase to the conclusion
 *                               (canonical link token "⊢").
 *
 * The library site renders these as dash-underlined spans that
 * cross-highlight with the structured statement rows (site/src/lib/docmd.ts
 * `renderNl`); every other consumer (search, embeddings, API.md, eval gold)
 * strips them via `stripNlCrosslinks`.
 *
 * Mirrors: CausalSmith/site/src/lib/docmd.ts (parseCrosslinks) and
 * tools/scripts/embed_library.py (strip_nl_crosslinks) — keep in sync.
 */

export interface NlCrosslinkSeg {
  text: string;
  /** Binder names this phrase links to ("⊢" = conclusion); null = plain prose. */
  links: string[] | null;
}

/**
 * Splits NL text into plain / linked segments. Scans for a `](hyp:…)` /
 * `](goal)` closer and walks BACK to its matching `[` counting nesting, so a
 * phrase may itself contain balanced brackets (`E[A·Y·(…)]`) — a single
 * regex cannot do this. A closer with no matching opener stays plain text;
 * ordinary markdown links (`[text](https://…)`) are untouched.
 */
export function parseNlCrosslinks(s: string): NlCrosslinkSeg[] {
  // Brackets inside code/math spans are CONTENT, not structure — interval
  // notation like `(0, 1/2]` would otherwise corrupt the balance walk. Scan a
  // masked copy (span brackets neutralized, same length) and slice the original.
  const masked = s.replace(/`[^`\n]+`|\$[^$\n]+\$/g, (t) => t.replace(/[[\]]/g, "•"));
  const segs: NlCrosslinkSeg[] = [];
  const closer = /\]\((?:hyp:([^()\s]+)|goal)\)/g;
  let plainStart = 0;
  let m: RegExpExecArray | null;
  while ((m = closer.exec(masked))) {
    let depth = 0;
    let open = -1;
    for (let i = m.index - 1; i >= plainStart; i--) {
      const c = masked[i];
      if (c === "]") depth++;
      else if (c === "[") {
        if (depth === 0) {
          open = i;
          break;
        }
        depth--;
      }
    }
    if (open < 0) continue;
    if (open > plainStart) segs.push({ text: s.slice(plainStart, open), links: null });
    const names = m[1] ? m[1].split(",").map((t) => t.trim()).filter(Boolean) : ["⊢"];
    segs.push({ text: s.slice(open + 1, m.index), links: names.length ? names : null });
    plainStart = closer.lastIndex;
  }
  if (plainStart < s.length) segs.push({ text: s.slice(plainStart), links: null });
  return segs;
}

/** Crosslink markup removed, phrase text kept — lossless for plain prose. */
export function stripNlCrosslinks(s: string): string {
  return parseNlCrosslinks(s)
    .map((g) => g.text)
    .join("");
}

/** All binder names referenced by crosslinks in `s` (excluding "⊢"). */
export function crosslinkNames(s: string): string[] {
  const out: string[] = [];
  for (const seg of parseNlCrosslinks(s)) {
    if (seg.links) out.push(...seg.links.filter((n) => n !== "⊢"));
  }
  return out;
}

/** Whether `s` links the conclusion via `[phrase](goal)`. */
export function linksGoal(s: string): boolean {
  return parseNlCrosslinks(s).some((seg) => seg.links?.includes("⊢"));
}

// ---------------------------------------------------------------------------
// binder-name extraction from an authored declaration source — for the lint.
// Minimal mirror of the site's leanStatement.ts scanner: strip comments, find
// the decl keyword, walk bracket-delimited binder groups up to the top-level
// `:`. Names are what a crosslink may reference.
// ---------------------------------------------------------------------------

export interface SourceBinder {
  names: string[];
  /** Explicit `( … )` binder whose type reads as a Prop — the rows the site
   * chips as "hyp" and the coverage check counts. Mirror of classifyChip. */
  isHyp: boolean;
}

function bracketDelta(c: string): number {
  if (c === "(" || c === "{" || c === "[" || c === "⦃") return 1;
  if (c === ")" || c === "}" || c === "]" || c === "⦄") return -1;
  return 0;
}

function stripLeanComments(text: string): string {
  let out = "";
  let i = 0;
  const n = text.length;
  while (i < n) {
    if (text[i] === "-" && text[i + 1] === "-") {
      while (i < n && text[i] !== "\n") {
        out += " ";
        i++;
      }
      continue;
    }
    if (text[i] === "/" && text[i + 1] === "-") {
      let depth = 1;
      out += "  ";
      i += 2;
      while (i < n && depth > 0) {
        if (text[i] === "/" && text[i + 1] === "-") {
          depth++;
          out += "  ";
          i += 2;
        } else if (text[i] === "-" && text[i + 1] === "/") {
          depth--;
          out += "  ";
          i += 2;
        } else {
          out += text[i] === "\n" ? "\n" : " ";
          i++;
        }
      }
      continue;
    }
    out += text[i];
    i++;
  }
  return out;
}

function topLevelIndexOf(text: string, ch: string): number {
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    depth += bracketDelta(text[i]);
    if (depth === 0 && text[i] === ch) return i;
  }
  return -1;
}

const PROP_HINT = /[≤≥≠↔∈⊆∀∃]|(?:^|[^:<>])=(?:[^=]|$)|\s<\s/;

/**
 * Binder groups of a theorem/lemma/def signature from its authored source
 * (docstring may still be present — it is stripped). Returns null when the
 * shape isn't confidently recognised (caller should skip, not fail).
 */
export function sourceBinders(rawSource: string): SourceBinder[] | null {
  const cleaned = stripLeanComments(rawSource);
  const m = cleaned.match(/\b(?:theorem|lemma|def|structure|class)\s+([^\s({[⦃:]+)/);
  if (!m || m.index === undefined) return null;
  let i = m.index + m[0].length;
  const uni = cleaned.slice(i).match(/^\s*\.\{[^}]*\}/);
  if (uni) i += uni[0].length;
  const n = cleaned.length;
  const out: SourceBinder[] = [];
  const skipWs = () => {
    while (i < n && /\s/.test(cleaned[i])) i++;
  };
  skipWs();
  while (i < n && bracketDelta(cleaned[i]) === 1) {
    const open = cleaned[i];
    const gStart = i;
    let depth = 0;
    do {
      depth += bracketDelta(cleaned[i]);
      i++;
    } while (i < n && depth > 0);
    if (depth !== 0) return null;
    const inner = cleaned.slice(gStart + 1, i - 1).trim();
    const colonIdx = topLevelIndexOf(inner, ":");
    if (colonIdx >= 0) {
      const names = inner.slice(0, colonIdx).trim().split(/\s+/).filter(Boolean);
      const typeText = inner.slice(colonIdx + 1).trim();
      const isHyp =
        open === "(" &&
        (names.every((t) => /^h/i.test(t) && t.length > 1) || PROP_HINT.test(typeText));
      if (names.length) out.push({ names, isHyp });
    }
    skipWs();
  }
  return out;
}

/**
 * Field names of a structure/class's `where` block (a crosslink in a
 * structure's docstring may target a field row, which the site renders
 * through the same row component as theorem hypotheses). Indentation-based,
 * mirroring the site's scanStructureFields: the first non-blank line after
 * `where` fixes the field indent; each line AT that indent opens a field.
 * Returns [] when there is no recognisable `where` block.
 */
export function sourceFieldNames(rawSource: string): string[] {
  const cleaned = stripLeanComments(rawSource);
  const m = cleaned.match(/\bwhere\b/);
  if (!m || m.index === undefined) return [];
  const lines = cleaned.slice(m.index + m[0].length).split("\n");
  const firstIdx = lines.findIndex((l) => l.trim().length > 0);
  if (firstIdx < 0) return [];
  const fieldIndent = lines[firstIdx].match(/^ */)![0].length;
  const out: string[] = [];
  for (let li = firstIdx; li < lines.length; li++) {
    const line = lines[li];
    if (line.trim().length === 0) continue;
    const indent = line.match(/^ */)![0].length;
    if (indent < fieldIndent) break;
    if (indent > fieldIndent) continue; // continuation of the previous field
    let t = line.trim();
    // bracket-wrapped instance/implicit field: `[decEqV : DecidableEq V]`
    if (/^[({[⦃]/.test(t)) t = t.slice(1, -1).trim();
    const colonIdx = topLevelIndexOf(t, ":");
    if (colonIdx <= 0) continue;
    out.push(...t.slice(0, colonIdx).trim().split(/\s+/).filter(Boolean));
  }
  return out;
}
