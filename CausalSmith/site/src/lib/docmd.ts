import katex from "katex";

/**
 * Minimal docstring → HTML renderer for Lean docstrings: paragraphs, `*`/`-` bullets,
 * backtick code spans, $…$ / $$…$$ KaTeX math. Everything else is escaped.
 * Build-time only (server-side KaTeX render).
 */

function esc(s: string): string {
  return s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}

function tex(src: string, display: boolean): string {
  try {
    return katex.renderToString(src, { displayMode: display, throwOnError: false });
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

function inline(s: string): string {
  // Render code/math spans into placeholders FIRST, then apply emphasis across the
  // whole (placeholder-bearing) string, then restore. This lets emphasis span a
  // code/math span — e.g. `**General-`n` identification.**` — which a
  // tokenize-then-emph-each-segment approach would split into unmatched `**`…`**`.
  // Placeholders use private-use chars (absent from docstrings, untouched by esc()
  // and the emph() regexes).
  const tokens: string[] = [];
  // Math delimiters: `$$…$$` / `\[…\]` (display) and `$…$` / `\(…\)` (inline).
  // `.tex`-sourced prose (paper abstracts/titles) uses `\(…\)`/`\[…\]`, while
  // codex-authored tldrs use `$…$` — accept both, plus backtick code spans.
  const re = /(\$\$[\s\S]+?\$\$|\\\[[\s\S]+?\\\]|\$[^$\n]+\$|\\\([\s\S]+?\\\)|`[^`\n]+`)/g;
  const withPlaceholders = s.replace(re, (tok) => {
    let html: string;
    if (tok.startsWith("$$")) html = tex(tok.slice(2, -2), true);
    else if (tok.startsWith("\\[")) html = tex(tok.slice(2, -2), true);
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

export function renderDoc(doc: string): string {
  const blocks = doc.trim().split(/\n\s*\n/);
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
    ? nl.replace(/\*\*([^*]+)\*\*/g, "$1").replace(/`([^`]+)`/g, "$1").replace(/^#+\s+/gm, "")
    : null;
}

export function nlOf(doc: string | null): string | null {
  if (!doc) return null;
  return doc.trim().split(/\n\s*\n/)[0].replace(/\s+/g, " ").trim() || null;
}
