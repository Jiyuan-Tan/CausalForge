import { renderDoc, renderTexLine } from "./docmd.js";

/**
 * P6 seminar-deck rendering: parse a bundle's `slides.md` (authored by the P6
 * pipeline stage, hand-editable) and render each slide's blocks to HTML.
 *
 * Format contract — MIRRORS `CausalSmith/tools/src/presentation/slides.ts`
 * (keep the two parsers in sync):
 *   - `---` on its own line separates slides;
 *   - first slide opens `# <talk title>`, later slides `## <slide title>`;
 *   - `@formal <obj_id>` injects the frozen formal-layer body verbatim;
 *   - `@informal <obj_id>: <headline>` is a labeled plain-language restatement;
 *   - `@figure <kebab-name>: <caption>` inlines `slides_assets/<name>.svg`, labeled
 *     "illustrative" (schematics only — see the pipeline's authoring lint);
 *   - everything else is markdown prose/bullets with inline math.
 */

export type SlideBlock =
  | { kind: "prose"; md: string }
  | { kind: "formal"; objId: string }
  | { kind: "informal"; objId: string; text: string }
  | { kind: "figure"; name: string; caption: string };

export interface Slide {
  title: string;
  blocks: SlideBlock[];
}

export interface SlidesDoc {
  talkTitle: string;
  slides: Slide[];
}

const FORMAL_RE = /^@formal\s+(\S+)\s*$/;
const INFORMAL_RE = /^@informal\s+(\S+)\s*:\s*(.*)$/;
const FIGURE_RE = /^@figure\s+([A-Za-z0-9_-]+)\s*:\s*(.*)$/;

export function parseSlidesMd(md: string): SlidesDoc {
  const chunks = md
    .split(/\n---[ \t]*\n/)
    .map((c) => c.trim())
    .filter((c) => c.length > 0);
  if (chunks.length === 0) throw new Error("slides.md is empty");
  const titleMatch = /^#\s+(.+)$/m.exec(chunks[0]);
  if (!titleMatch || !chunks[0].trimStart().startsWith("# ")) {
    throw new Error("slides.md must open with a `# <talk title>` title slide");
  }
  const talkTitle = titleMatch[1].trim();
  const slides: Slide[] = [];
  for (const [i, chunk] of chunks.entries()) {
    const lines = chunk.split("\n");
    let title: string;
    if (i === 0) {
      title = talkTitle;
      lines.shift();
    } else {
      const m = /^##\s+(.+)$/.exec(lines[0] ?? "");
      if (!m) throw new Error(`slide ${i + 1} does not open with a \`## <title>\` heading`);
      title = m[1].trim();
      lines.shift();
    }
    const blocks: SlideBlock[] = [];
    let prose: string[] = [];
    const flush = () => {
      const text = prose.join("\n").trim();
      if (text) blocks.push({ kind: "prose", md: text });
      prose = [];
    };
    for (const line of lines) {
      const f = FORMAL_RE.exec(line);
      const inf = INFORMAL_RE.exec(line);
      const fig = FIGURE_RE.exec(line);
      if (f) {
        flush();
        blocks.push({ kind: "formal", objId: f[1].replace(/^obj:/, "") });
      } else if (inf) {
        flush();
        blocks.push({ kind: "informal", objId: inf[1].replace(/^obj:/, ""), text: inf[2].trim() });
      } else if (fig) {
        flush();
        blocks.push({ kind: "figure", name: fig[1], caption: fig[2].trim() });
      } else {
        prose.push(line);
      }
    }
    flush();
    slides.push({ title, blocks });
  }
  return { talkTitle, slides };
}

/** Renders a frozen formal-layer BODY (paper TeX) to HTML: cross-references are
 *  flattened to plain ids (the deck has no label targets, including comma lists
 *  `\cref{obj:a,obj:b}`), `itemize`/`enumerate` become real lists, display math
 *  stays display. Built on docmd's tokenizer, so `\(…\)`/`\[…\]`/`$…$` all render
 *  (KaTeX handles `cases`/`array`/`aligned` INSIDE math; text-mode structures are
 *  what must be translated here or they leak as raw `\item`/`\cref` source). */
export function renderFormalBody(
  body: string,
  resolveRef?: (objId: string) => { href: string; label: string } | null,
): string {
  // Cross-references become placeholder tokens that survive renderTexLine's
  // escaping, then resolve to paper-page links (or plain ids when unresolvable).
  // Inside MATH segments a token would be typeset by KaTeX (each char its own
  // <mi>, the post-pass regex never matches the rendered HTML) — so math-mode
  // crefs flatten to \text{<id>} instead of linking.
  const stripIds = (ids: string) => ids.split(",").map((t) => t.trim().replace(/^obj:/, ""));
  const flat = body
    .replace(/~(?=\\(?:[cC]|eq)?ref\{)/g, " ")
    .replace(
      /(\\\[[\s\S]*?\\\]|\\\([\s\S]*?\\\)|\$\$[\s\S]*?\$\$|\\begin\{(align\*?|equation\*?|gather\*?|multline\*?)\}[\s\S]*?\\end\{\2\})/g,
      (seg) =>
        seg.replace(/\\(?:[cC]|eq)?ref\{([^}]*)\}/g, (_, ids: string) =>
          `\\text{${stripIds(ids).join(", ")}}`,
        ),
    )
    .replace(/\\(?:[cC]|eq)?ref\{([^}]*)\}/g, (_, ids: string) =>
      stripIds(ids).map((id) => `⟦ref:${id}⟧`).join(", "),
    )
    .replace(/\\label\{[^}]*\}/g, "");
  const linkRefs = (html: string): string =>
    html.replace(/⟦ref:([^⟦⟧]+)⟧/g, (_, id: string) => {
      const r = resolveRef?.(id) ?? null;
      const escHtml = (s: string) =>
        s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
      return r ? `<a class="formal-ref" href="${escHtml(r.href)}">${escHtml(r.label)}</a>` : id;
    });
  const parts: string[] = [];
  const listRe = /\\begin\{(itemize|enumerate)\}([\s\S]*?)\\end\{\1\}/g;
  let last = 0;
  for (let m = listRe.exec(flat); m; m = listRe.exec(flat)) {
    pushPara(parts, flat.slice(last, m.index));
    const tag = m[1] === "enumerate" ? "ol" : "ul";
    const items = m[2]
      .split(/\\item\b/)
      .map((s) => s.trim())
      .filter(Boolean)
      // \item[Label.] optional argument becomes a bold lead-in, not literal [..]
      .map((s) => s.replace(/^\[([^\]]*)\]\s*/, (_, lab: string) => `\\textbf{${lab}} `));
    parts.push(`<${tag}>${items.map((it) => `<li>${renderTexLine(it)}</li>`).join("")}</${tag}>`);
    last = m.index + m[0].length;
  }
  pushPara(parts, flat.slice(last));
  return linkRefs(parts.join("\n"));
}

function pushPara(parts: string[], s: string): void {
  const t = s.trim();
  if (t) parts.push(`<p>${renderTexLine(t)}</p>`);
}

export { titleCase } from "./docmd.js";

/** Renders a slide's markdown prose (bullets/paragraphs + inline math). */
export function renderSlideProse(md: string): string {
  return renderDoc(md);
}

/** Defense-in-depth over the pipeline's SVG lint before inlining a figure asset
 *  into the page: reject scripts, non-fragment references, and raster payloads.
 *  Returns null (→ placeholder) rather than shipping a suspect asset. */
export function safeFigureSvg(svg: string): string | null {
  const start = svg.indexOf("<svg");
  const end = svg.lastIndexOf("</svg>");
  if (start < 0 || end < start) return null;
  const doc = svg.slice(start, end + "</svg>".length);
  if (
    /<script\b/i.test(doc) ||
    /\bhref\s*=\s*["'](?!#)/i.test(doc) ||
    /url\s*\(\s*["']?(?!#)/i.test(doc) ||
    /<image\b/i.test(doc) ||
    /\bon[a-z]+\s*=/i.test(doc) ||
    // scriptless external-load vectors: foreignObject smuggles HTML (iframes),
    // src= loads external resources, @import needs no url() wrapper
    /<foreignObject\b/i.test(doc) ||
    /<iframe\b/i.test(doc) ||
    /\bsrc\s*=/i.test(doc) ||
    /@import\b/i.test(doc)
  ) {
    return null;
  }
  return doc;
}
