import { describe, it, expect, vi, afterEach } from "vitest";
import {
  parseBib,
  citedKeys,
  verifyEntry,
  defaultLookup,
  UNREACHABLE,
  canonicalizeBibEntry,
  type BibEntry,
} from "../src/presentation/citations.js";

const BIB = `@article{robins1994,
  title = {Estimation of Regression Coefficients When Some Regressors Are Not Always Observed},
  author = {Robins, James M. and Rotnitzky, Andrea and Zhao, Lue Ping},
  journal = {JASA}, year = {1994}, doi = {10.1080/01621459.1994.10476818}
}
@misc{fake2025, title = {A Paper That Does Not Exist}, author = {Nobody, A.}, year = {2025}
}`;

describe("citations", () => {
  it("parses bib entries", () => {
    const entries = parseBib(BIB);
    expect(entries.map((e) => e.key)).toEqual(["robins1994", "fake2025"]);
    expect(entries[0].fields.year).toBe("1994");
    expect(entries[0].fields.author).toContain("Robins");
  });

  it("parses one-line entries and quoted fields", () => {
    const entries = parseBib(`@article{k, title = "X", author = {Robins}, year = {1994}}`);
    expect(entries).toEqual([
      {
        key: "k",
        type: "article",
        fields: { title: "X", author: "Robins", year: "1994" },
      },
    ]);
  });

  it("finds cited keys in tex including strays", () => {
    const tex = "as shown by \\citet{robins1994} and \\citep[see][]{robins1994, missing2020}";
    expect([...citedKeys(tex)].sort()).toEqual(["missing2020", "robins1994"]);
  });

  it("verifies via injected lookup: exact / minor / major", async () => {
    const lookup = async (e: BibEntry) =>
      e.key === "robins1994"
        ? {
            title: "Estimation of regression coefficients when some regressors are not always observed",
            authorFamily: "Robins",
            year: 1994,
          }
        : null;
    const entries = parseBib(BIB);
    expect((await verifyEntry(entries[0], lookup)).verdict).toBe("exact");
    expect((await verifyEntry(entries[1], lookup)).verdict).toBe("major");
    const wrongYear = async () => ({ title: entries[0].fields.title, authorFamily: "Robins", year: 2001 });
    expect((await verifyEntry(entries[0], wrongYear)).verdict).toBe("minor");
  });

  it("id-authoritative record: a title mismatch is a field fix (minor), not a wrong-source drop", async () => {
    // Books store only the short title in Crossref, so the DOI-fetched record's title differs
    // from the entry's full title-with-subtitle. As long as the author corroborates, the DOI
    // confirms the source — keep it (minor), never drop it (major).
    const book: BibEntry = {
      key: "imbens2015",
      type: "book",
      fields: {
        title: "Causal Inference for Statistics, Social, and Biomedical Sciences: An Introduction",
        author: "Imbens, Guido W. and Rubin, Donald B.",
        year: "2015",
        doi: "10.1017/CBO9781139025751",
      },
    };
    const shortTitleByDoi = async () => ({
      title: "Causal Inference for Statistics, Social, and Biomedical Sciences",
      authorFamily: "Imbens",
      year: 2015,
      authoritative: true,
    });
    expect((await verifyEntry(book, shortTitleByDoi)).verdict).toBe("minor");
  });

  it("id-authoritative but author also mismatches stays major (guards a stray DOI hitting another work)", async () => {
    const book: BibEntry = {
      key: "imbens2015",
      type: "book",
      fields: { title: "Causal Inference ...", author: "Imbens, Guido W.", year: "2015", doi: "10.x/y" },
    };
    const otherPaperByDoi = async () => ({
      title: "A completely different paper",
      authorFamily: "Smith",
      year: 2015,
      authoritative: true,
    });
    expect((await verifyEntry(book, otherPaperByDoi)).verdict).toBe("major");
  });

  it("UNREACHABLE registry is non-blocking (minor), not a hallucination rejection", async () => {
    const entry: BibEntry = {
      key: "fan2025",
      type: "misc",
      fields: { title: "Some Real Paper", author: "Fan, X.", year: "2025", eprint: "2502.06008" },
    };
    const v = await verifyEntry(entry, async () => UNREACHABLE);
    expect(v.verdict).toBe("minor");
    expect(v.detail).toMatch(/unreachable/i);
  });

  it("normalizes fields only from an authoritative id record", () => {
    const rec = { title: "Canonical Title", authorFamily: "Robins", author: "Robins, James", year: 1995, authoritative: true };
    const fixed = canonicalizeBibEntry(BIB, "robins1994", rec)!;
    const entry = parseBib(fixed)[0];
    expect(entry.fields.title).toBe("Canonical Title");
    expect(entry.fields.author).toBe("Robins, James");
    expect(entry.fields.year).toBe("1995");
    expect(entry.fields.doi).toBe("10.1080/01621459.1994.10476818");
    expect(canonicalizeBibEntry(BIB, "robins1994", { ...rec, authoritative: false })).toBeNull();
  });

  it("decodes and TeX-escapes ampersands in authoritative metadata", () => {
    const rec = { title: "Patents-R &amp; D Relationship", authorFamily: "Hausman", year: 1984, authoritative: true };
    const fixed = canonicalizeBibEntry(BIB, "robins1994", rec)!;
    expect(fixed).toContain("Patents-R \\& D Relationship");
    expect(fixed).not.toContain("&amp;");
  });
});

describe("defaultLookup: transient-unreachable vs definitively-absent", () => {
  const realFetch = globalThis.fetch;
  afterEach(() => {
    globalThis.fetch = realFetch;
    vi.useRealTimers();
  });

  // A wrong Crossref title-query hit — the record the OLD fallback would have laundered into a "major".
  const wrongCrossrefHit = {
    ok: true,
    status: 200,
    json: async () => ({
      message: { items: [{ title: ["A Completely Different Paper"], author: [{ family: "Other" }], issued: { "date-parts": [[2024]] } }] },
    }),
    text: async () => "",
  };
  const arxivEmptyFeed = {
    ok: true,
    status: 200,
    json: async () => ({}),
    text: async () => "<feed><title>ArXiv Query</title></feed>", // no entry <title> → no record
  };

  const runLookup = async (entry: BibEntry) => {
    vi.useFakeTimers();
    const p = defaultLookup(entry);
    await vi.runAllTimersAsync(); // drive politeFetch's throttle + backoff sleeps
    return p;
  };

  it("arXiv id unreachable (429) → UNREACHABLE, never falls back to the wrong title hit", async () => {
    const crossref = vi.fn(async () => wrongCrossrefHit);
    globalThis.fetch = vi.fn(async (url: string | URL) => {
      const u = String(url);
      if (u.includes("export.arxiv.org")) return { ok: false, status: 429 } as unknown as Response;
      if (u.includes("api.crossref.org")) return crossref() as unknown as Promise<Response>;
      return { ok: false, status: 404 } as unknown as Response;
    }) as unknown as typeof fetch;

    const entry: BibEntry = {
      key: "fan2025",
      type: "misc",
      fields: { title: "Causal Inference under Interference", author: "Fan, X.", year: "2025", eprint: "2502.06008" },
    };
    const rec = await runLookup(entry);
    expect(rec).toBe(UNREACHABLE); // NOT the wrong Crossref paper
    expect(crossref).not.toHaveBeenCalled(); // the laundering title-query never ran
  });

  it("arXiv id definitively absent (reachable, empty feed) → still title-checked → fabricated id caught (major)", async () => {
    globalThis.fetch = vi.fn(async (url: string | URL) => {
      const u = String(url);
      if (u.includes("export.arxiv.org")) return arxivEmptyFeed as unknown as Response;
      if (u.includes("api.crossref.org")) return wrongCrossrefHit as unknown as Response;
      return { ok: false, status: 404 } as unknown as Response;
    }) as unknown as typeof fetch;

    const entry: BibEntry = {
      key: "fake2030",
      type: "misc",
      fields: { title: "A Paper That Does Not Exist", author: "Nobody, A.", year: "2030", eprint: "9999.99999" },
    };
    vi.useFakeTimers();
    const p = verifyEntry(entry, defaultLookup);
    await vi.runAllTimersAsync();
    expect((await p).verdict).toBe("major"); // reachable-but-absent id is not laundered to non-blocking
  });
});
