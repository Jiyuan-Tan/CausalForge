/**
 * KaTeX configuration shared by the paper renderer and its client-side fallback.
 *
 * Deliberately free of a top-level `import katex`: the paper page's inline script imports
 * `katexOptions` from here, and a static katex import would pull katex into that module's
 * critical path — a failed katex load would then abort the script before the drawer is
 * wired. The page loads katex lazily; this module only describes how to call it.
 */

// Type-only: erased at compile time, so it does not pull katex into a client bundle.
import type { KatexOptions } from "katex";

/**
 * Math symbols the papers' LaTeX preamble declares but KaTeX does not ship.
 *
 * The PDF gets these from a symbol font (`\DeclareMathSymbol` in `paper.tex`); the web
 * renderer has no such font, so each one needs a KaTeX-expressible equivalent here.
 * Without an entry KaTeX cannot parse the formula at all and the whole block degrades to
 * red raw TeX, so a preamble symbol added upstream must be mirrored here — the paper-math
 * test fails on any control sequence the bundles use and this map does not cover.
 */
export const KATEX_MACROS: Record<string, string> = {
  // Truncated (natural-number) subtraction, a ∸ b = max{a-b,0}.
  "\\dotminus": "\\mathbin{\\dot{-}}",
};

/** Undoes the HTML entity escaping pandoc applies inside `\(…\)` math spans. */
export function decodeEntities(s: string): string {
  return s
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">")
    .replace(/&quot;/g, '"')
    .replace(/&#0*39;|&#x0*27;/gi, "'")
    .replace(/&#0*(\d+);/g, (_, d) => String.fromCodePoint(Number(d)))
    .replace(/&#x([0-9a-f]+);/gi, (_, h) => String.fromCodePoint(parseInt(h, 16)))
    .replace(/&amp;/g, "&");
}

/** The TeX source of one pandoc math span: entities decoded, delimiters and embedded
 *  cross-reference anchors normalised into something KaTeX can parse. */
export function spanTex(body: string): string {
  return decodeEntities(body)
    .replace(/^\s*\\\(|\\\)\s*$/g, "")
    .replace(/^\s*\\\[|\\\]\s*$/g, "")
    // A cross-reference (\ref{obj:X}) that sits INSIDE a math span (e.g. the
    // rollout-law-class definition's "\text{satisfies Assumptions~\ref{…}}")
    // is emitted as an <a class="objref"> HTML anchor. KaTeX cannot parse raw
    // HTML, so convert each anchor to KaTeX's own \href (rendered as a clickable
    // link; trusted below for internal #-fragment targets only) instead of
    // letting the whole block fall back to raw LaTeX.
    .replace(
      /<a\b[^>]*\bhref="([^"]*)"[^>]*>([\s\S]*?)<\/a>/g,
      (_m, url: string, txt: string) => `\\href{${url}}{${txt.replace(/<[^>]+>/g, "").trim()}}`,
    )
    .trim();
}

/** KaTeX options shared by every paper-math render (build-time and client fallback). */
export function katexOptions(display: boolean, throwOnError = false): KatexOptions {
  return {
    displayMode: display,
    throwOnError,
    macros: { ...KATEX_MACROS },
    trust: (ctx) => ctx.command === "\\href" && ctx.url.startsWith("#"),
  };
}

