import { describe, it, expect } from "vitest";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { join, resolve } from "node:path";
import katex from "katex";
import { katexOptions, spanTex } from "../src/lib/katexConfig.js";
import { renderMath } from "../src/lib/paperMath.js";

const PRESENTATION = resolve(import.meta.dirname, "..", "..", "doc", "presentation");

describe("paper math rendering", () => {
  it("renders truncated subtraction, which KaTeX has no built-in symbol for", () => {
    const html = renderMath('<span class="math inline">\\(M\\dotminus 2\\)</span>');
    expect(html).not.toContain("katex-error"); // the symbol is defined, not raw red TeX
    expect(html).toContain("accent"); // a dotted minus: an accent over the binary minus
  });

  it("converts an in-math cross-reference anchor into a KaTeX link", () => {
    const html = renderMath(
      '<span class="math inline">\\(\\text{see }<a href="#obj:T-1">Theorem 1</a>\\)</span>',
    );
    expect(html).toContain('href="#obj:T-1"');
  });

  // Every formula in every bundle must PARSE. KaTeX's throwOnError:false would otherwise
  // print an undefined control sequence as red raw TeX on the page while the PDF, whose
  // preamble declares the symbol, looks fine — the failure is invisible to the LaTeX side.
  // A new preamble symbol therefore needs a KATEX_MACROS entry, and this test says so.
  it("parses every math span in every published bundle", () => {
    if (!existsSync(PRESENTATION)) return; // bundles not present in this checkout
    const failures: string[] = [];
    for (const id of readdirSync(PRESENTATION)) {
      const body = join(PRESENTATION, id, "paper_body.html");
      if (!existsSync(body)) continue;
      const html = readFileSync(body, "utf8");
      for (const m of html.matchAll(/<span class="math (inline|display)">([\s\S]*?)<\/span>/g)) {
        const tex = spanTex(m[2]);
        try {
          katex.renderToString(tex, katexOptions(m[1] === "display", true));
        } catch (e) {
          failures.push(`${id}: ${(e as Error).message}\n    ${tex.replace(/\s+/g, " ").slice(0, 120)}`);
        }
      }
    }
    expect(failures.slice(0, 5).join("\n")).toBe("");
  });
});
