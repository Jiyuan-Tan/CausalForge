import { gzipSync } from "node:zlib";

import { describe, it, expect } from "vitest";

import { resolveCitedTarget, type FetchBytes } from "../../src/formalization/citation_fetch.js";
import type { Citation } from "../../src/formalization/plan/schema.js";

const base: Citation = {
  id: "cite:demo",
  title: "A Result",
  authors: "Author",
  year: 2020,
  locator: "Theorem 3.1",
};

const neverFetch: FetchBytes = async () => null;

/** Build a ustar archive holding each `[name, content]` member in order. */
function tar(...members: Array<[string, string]> | [string, string]): Uint8Array {
  const entries: Array<[string, string]> =
    typeof members[0] === "string"
      ? [members as [string, string]]
      : (members as Array<[string, string]>);
  const enc = new TextEncoder();
  const blocks: number[] = [];
  for (const [name, content] of entries) {
    const data = enc.encode(content);
    const header = new Uint8Array(512);
    header.set(enc.encode(name), 0);
    header.set(enc.encode("0000644\0"), 100); // mode
    header.set(enc.encode(data.length.toString(8).padStart(11, "0") + "\0"), 124); // size (octal)
    header.set(enc.encode("ustar\0"), 257); // magic
    const padded = new Uint8Array(Math.ceil(data.length / 512) * 512);
    padded.set(data);
    blocks.push(...header, ...padded);
  }
  return new Uint8Array([...blocks, ...new Uint8Array(1024)]); // two zero end blocks
}

describe("resolveCitedTarget", () => {
  it("is verbatim-first (attested) even when an arxiv handle exists", async () => {
    const c = { ...base, arxiv: "2207.11825", verbatim_statement: "R_n ≥ c · n^{-2α/(2α+1)}" };
    const r = await resolveCitedTarget(c, neverFetch);
    expect(r.mode).toBe("attested");
    expect(r.text).toContain("R_n");
  });

  it("falls back to a best-effort fetched gzipped-tar e-print", async () => {
    const archive = gzipSync(Buffer.from(tar("main.tex", "\\begin{lemma}\\label{l1} foo \\end{lemma}")));
    const fetchStub: FetchBytes = async (url) =>
      url.endsWith("/e-print/2207.11825") ? new Uint8Array(archive) : null;
    const r = await resolveCitedTarget({ ...base, arxiv: "2207.11825" }, fetchStub);
    expect(r.mode).toBe("fetched");
    expect(r.text).toContain("\\begin{lemma}");
  });

  it("leads a multi-file bundle with the document root, not an alphabetically-first macro file", async () => {
    // Regression (stat_doseresponse_minimax_elbow, 2026-07-29). A real 42.9 MB arXiv bundle
    // unpacked with `amssym.tex` first in tar order; every `.tex` was concatenated blindly
    // and the D0.5 referee sees only the LEADING slice of the result, so it was handed a
    // symbol-macro fragment and honestly reported it could not verify a citation that was
    // in fact accurate. Ordering is load-bearing precisely because the consumer truncates.
    const archive = gzipSync(Buffer.from(tar(
      ["amssym.tex", `\\def\\Bbb{\\bf}\n${"% padding macro line\n".repeat(400)}`],
      ["paper/main.tex", "\\documentclass{article}\\begin{document}\\input{section3_theory}\\end{document}"],
      ["paper/section3_theory.tex", "\\section{Theory}\\begin{theorem}\\label{thm1} the cited result \\end{theorem}"],
    )));
    const fetchStub: FetchBytes = async (url) =>
      url.endsWith("/e-print/2210.06448") ? new Uint8Array(archive) : null;

    const r = await resolveCitedTarget({ ...base, arxiv: "2210.06448" }, fetchStub);

    expect(r.mode).toBe("fetched");
    // the window the referee actually reads must open on the document, not the macros
    expect(r.text.slice(0, 6000)).toContain("\\begin{document}");
    expect(r.text.slice(0, 6000)).toContain("the cited result");
    expect(r.text.indexOf("\\documentclass")).toBeLessThan(r.text.indexOf("\\def\\Bbb"));
    // nothing is dropped — the macro file is still present, just last
    expect(r.text).toContain("\\def\\Bbb");
  });

  it("accepts a single uncompressed .tex e-print", async () => {
    const fetchStub: FetchBytes = async () =>
      new Uint8Array(Buffer.from("\\documentclass{article}\\begin{theorem} bar \\end{theorem}"));
    const r = await resolveCitedTarget({ ...base, arxiv: "1234.5678" }, fetchStub);
    expect(r.mode).toBe("fetched");
    expect(r.text).toContain("theorem");
  });

  it("is unverifiable when no verbatim statement and no fetchable source", async () => {
    const r = await resolveCitedTarget(base, neverFetch);
    expect(r.mode).toBe("unverifiable");
    expect(r.text).toBe("");
  });

  it("is unverifiable when the fetch returns non-tex bytes", async () => {
    const fetchStub: FetchBytes = async () => new Uint8Array([0, 1, 2, 3, 4, 5]);
    const r = await resolveCitedTarget({ ...base, arxiv: "9999.9999" }, fetchStub);
    expect(r.mode).toBe("unverifiable");
  });
});
