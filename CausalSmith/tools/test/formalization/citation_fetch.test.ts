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

/** Build a one-member ustar archive holding `name` → `content`. */
function tar(name: string, content: string): Uint8Array {
  const enc = new TextEncoder();
  const data = enc.encode(content);
  const header = new Uint8Array(512);
  header.set(enc.encode(name), 0);
  header.set(enc.encode("0000644\0"), 100); // mode
  header.set(enc.encode(data.length.toString(8).padStart(11, "0") + "\0"), 124); // size (octal)
  header.set(enc.encode("ustar\0"), 257); // magic
  const padded = new Uint8Array(Math.ceil(data.length / 512) * 512);
  padded.set(data);
  const end = new Uint8Array(1024); // two zero blocks
  return new Uint8Array([...header, ...padded, ...end]);
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
