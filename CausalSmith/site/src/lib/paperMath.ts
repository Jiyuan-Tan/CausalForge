import katex from "katex";
import { katexOptions, spanTex } from "./katexConfig.js";

/**
 * Renders every pandoc math span in a paper body at BUILD TIME so formulas are baked into
 * the static HTML (no client-side KaTeX dependency, immune to load order / cache / the
 * HTML-entity-escaped `&gt;`/`&lt;` that pandoc emits inside `\(...\)`). A span KaTeX
 * rejects is left raw for the page's client-side fallback to retry.
 */
export function renderMath(html: string): string {
  return html.replace(
    /<span class="math (inline|display)">([\s\S]*?)<\/span>/g,
    (whole, mode: string, body: string) => {
      const tex = spanTex(body);
      try {
        return katex.renderToString(tex, katexOptions(mode === "display"));
      } catch {
        return whole; // leave raw; client-side fallback will retry
      }
    },
  );
}
