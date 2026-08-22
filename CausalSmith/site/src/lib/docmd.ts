import katex from "katex";
import { KATEX_MACROS } from "./katexConfig.js";

/**
 * Minimal docstring → HTML renderer for Lean docstrings: paragraphs, `*`/`-` bullets,
 * backtick code spans, $…$ / $$…$$ KaTeX math. Everything else is escaped.
 * Build-time only (server-side KaTeX render).
 */

function esc(s: string): string {
  // Quotes must be escaped too: esc() output is interpolated into HTML
  // attributes (renderNl's data-links), where a bare `"` closes the attribute
  // early and injects arbitrary attributes (audit finding, 2026-08-17).
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

function tex(src: string, display: boolean): string {
  try {
    return katex.renderToString(src, {
      displayMode: display,
      throwOnError: false,
      macros: { ...KATEX_MACROS },
    });
  } catch {
    return `<code>${esc(src)}</code>`;
  }
}

/** Renders inline content: math and code spans tokenized first, plain text escaped. */
// markdown emphasis in already-escaped plain text: **bold** and *italic*,
// plus the common LaTeX text macros that leak in from .tex-sourced prose
// (abstracts/titles): \emph/\textit → <em>, \textbf → <strong>, \texttt → <code>.
function emph(escaped: string): string {
  return escaped
    .replace(/\\(?:emph|textit|textsl)\{([^{}]*)\}/g, "<em>$1</em>")
    .replace(/\\(?:textbf|textsc)\{([^{}]*)\}/g, "<strong>$1</strong>")
    .replace(/\\texttt\{([^{}]*)\}/g, "<code>$1</code>")
    .replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>")
    .replace(/(^|[\s(])\*([^*\s][^*]*)\*(?=[\s).,;:]|$)/g, "$1<em>$2</em>");
}

// Private-use delimiters wrapping a token index: absent from docstrings,
// untouched by esc()/emph(), and unambiguous (a bare number would collide
// with prose digits like "Firpo 2007").
const TOK_OPEN = String.fromCharCode(0xe000);
const TOK_CLOSE = String.fromCharCode(0xe001);

function inline(s: string, compact = false): string {
  // Render code/math spans into placeholders FIRST, then apply emphasis across the
  // whole (placeholder-bearing) string, then restore. This lets emphasis span a
  // code/math span — e.g. `**General-`n` identification.**` — which a
  // tokenize-then-emph-each-segment approach would split into unmatched `**`…`**`.
  // Placeholders use private-use chars (absent from docstrings, untouched by esc()
  // and the emph() regexes).
  const tokens: string[] = [];
  // Strip any pre-existing placeholder char from the input, or it would be read back as a
  // token index and silently swap in the wrong span (or `undefined`). Docstrings never
  // contain these; pipeline-authored JSON now flows through here too, so do not assume it.
  s = s.replace(new RegExp(`[${TOK_OPEN}${TOK_CLOSE}]`, "g"), "");
  // Math delimiters: `$$…$$` / `\[…\]` (display) and `$…$` / `\(…\)` (inline).
  // `.tex`-sourced prose (paper abstracts/titles) uses `\(…\)`/`\[…\]`, while
  // codex-authored tldrs use `$…$` — accept both, plus backtick code spans.
  const re = /(\$\$[\s\S]+?\$\$|\\\[[\s\S]+?\\\]|\$[^$\n]+\$|\\\([\s\S]+?\\\)|`[^`\n]+`)/g;
  const withPlaceholders = s.replace(re, (tok) => {
    // `compact` demotes display math to inline: in a one-line index row a centred
    // block would break the row, and the surrounding layout supplies the emphasis.
    let html: string;
    if (tok.startsWith("$$")) html = tex(tok.slice(2, -2), !compact);
    else if (tok.startsWith("\\[")) html = tex(tok.slice(2, -2), !compact);
    else if (tok.startsWith("\\(")) html = tex(tok.slice(2, -2), false);
    else if (tok.startsWith("$")) html = tex(tok.slice(1, -1), false);
    else html = `<code>${esc(tok.slice(1, -1))}</code>`;
    tokens.push(html);
    return `${TOK_OPEN}${tokens.length - 1}${TOK_CLOSE}`;
  });
  return emph(esc(withPlaceholders)).replace(
    new RegExp(`${TOK_OPEN}(\\d+)${TOK_CLOSE}`, "g"),
    (_, i) => tokens[Number(i)],
  );
}

/** Renders a one-line TeX-bearing string (paper title/abstract) to HTML:
 *  $…$ math via KaTeX, `\ref{obj:X}` flattened to the plain id (the index
 *  page has no label targets), everything else escaped. */
export function renderTexLine(s: string): string {
  return inline(s.replace(/~?\\ref\{obj:([\w-]+)\}/g, "$1"));
}

/** Renders a TeX-bearing string for a compact index row (the Formal-layer panel's
 *  NL column): same tokenizer as `renderTexLine`, but display math is demoted to
 *  inline so a row stays a row, and EVERY cross-reference form is flattened, not just
 *  `\ref{obj:…}` — the panel has no label targets, so a surviving `\cref{…}` or
 *  `Theorem~\ref{thm:…}` would print as raw source. The `~` becomes a space. */
export function renderTexCompact(s: string): string {
  const flat = s
    .replace(/~(?=\\(?:[cC]|eq)?ref\{)/g, " ")
    .replace(/\\(?:[cC]|eq)?ref\{(?:obj:)?([\w:.-]+)\}/g, "$1");
  return inline(flat, true);
}

/** Renders a Formal-layer row's LABEL. A `symbol` row's label IS a formula and is written
 *  bare, without delimiters (`\Delta_r(p)`); every other label is plain text ("Setup S-1").
 *  A label carrying a macro is therefore rendered as one whole formula — no guessing where
 *  the math starts. Anything KaTeX rejects falls back to escaped text. */
export function renderLabel(s: string): string {
  if (!/\\[a-zA-Z]/.test(s)) return esc(s);
  const tex = s.replace(/^\s*\\\(|\\\)\s*$/g, "").trim();
  try {
    return katex.renderToString(tex, { throwOnError: true, macros: { ...KATEX_MACROS } });
  } catch {
    return esc(s);
  }
}

// ── NL ↔ Lean crosslink markup ──────────────────────────────────────────
// Authored in the Lean docstring's first paragraph (docstring-canonical):
//   [phrase](hyp:name[,name…])  links the phrase to the statement row(s)
//                               binding those names;
//   [phrase](goal)              links the phrase to the conclusion block
//                               (canonical link token "⊢").
// The decl card renders these as dash-underlined spans that cross-highlight
// with the structured statement rows; every other consumer strips them.
// Mirrors: CausalSmith/tools/src/shared/nl_crosslinks.ts, tools/scripts/
// embed_library.py — keep the three in sync.

export interface CrosslinkSeg {
  text: string;
  /** Binder names this phrase links to ("⊢" = conclusion); null = plain prose. */
  links: string[] | null;
}

/**
 * Splits NL text into plain / linked segments. Scans for a `](hyp:…)` /
 * `](goal)` closer and walks BACK to its matching `[` counting nesting, so a
 * phrase may itself contain balanced brackets (`E[A·Y·(…)]`) — a single
 * regex cannot do this. A closer with no matching opener stays plain text.
 */
export function parseCrosslinks(s: string): CrosslinkSeg[] {
  // Brackets inside code/math spans are CONTENT, not structure — interval
  // notation like `(0, 1/2]` would otherwise corrupt the balance walk. Scan a
  // masked copy (span brackets neutralized, same length) and slice the original.
  const masked = s.replace(/`[^`\n]+`|\$[^$\n]+\$/g, (t) => t.replace(/[[\]]/g, "•"));
  const segs: CrosslinkSeg[] = [];
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

/** Crosslink markup removed, phrase text kept — for every consumer that is
 *  not the decl card (module docs, search snippets, API.md, plain text). */
export function stripCrosslinks(s: string): string {
  return parseCrosslinks(s)
    .map((g) => g.text)
    .join("");
}

/**
 * Renders a decl's NL first paragraph with crosslink spans. Each linked
 * phrase becomes `<span class="nl-link" data-links="…">` (space-separated
 * binder names; "⊢" = conclusion) that the library page cross-highlights
 * with the structured statement rows. Falls back to `renderDoc` when the
 * paragraph carries no crosslinks.
 */
export function renderNl(nl: string): string {
  const segs = parseCrosslinks(nl);
  if (!segs.some((g) => g.links)) return renderDoc(nl);
  const html = segs
    .map((g) =>
      g.links
        ? `<span class="nl-link" data-links="${esc(g.links.join(" "))}" tabindex="0">${inline(g.text)}</span>`
        : inline(g.text),
    )
    .join("");
  return `<p>${html}</p>`;
}

export function renderDoc(doc: string): string {
  const blocks = stripCrosslinks(doc).trim().split(/\n\s*\n/);
  const html: string[] = [];
  for (const b of blocks) {
    const lines = b.split("\n");
    const hm = b.match(/^\s*(#{1,6})\s+(.*)$/);
    if (hm && lines.length === 1) {
      // markdown section headers in module docs render as small headings
      html.push(`<h4 class="doc-h">${inline(hm[2])}</h4>`);
      continue;
    }
    if (lines.every((l) => /^\s*[*-]\s+/.test(l))) {
      const items = lines.map((l) => `<li>${inline(l.replace(/^\s*[*-]\s+/, ""))}</li>`);
      html.push(`<ul>${items.join("")}</ul>`);
    } else {
      html.push(`<p>${inline(b)}</p>`);
    }
  }
  return html.join("\n");
}

/** First paragraph of a docstring = the NL translation (extraction convention). */
/** Marker-free single-line NL (for contexts that interpolate raw text:
 *  helper one-liners, search snippets). */
export function nlPlain(doc: string | null): string | null {
  const nl = nlOf(doc);
  return nl
    ? stripCrosslinks(nl)
        .replace(/\*\*([^*]+)\*\*/g, "$1")
        .replace(/`([^`]+)`/g, "$1")
        .replace(/^#+\s+/gm, "")
    : null;
}

export function nlOf(doc: string | null): string | null {
  if (!doc) return null;
  return doc.trim().split(/\n\s*\n/)[0].replace(/\s+/g, " ").trim() || null;
}
