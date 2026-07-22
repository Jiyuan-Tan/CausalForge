import { describe, expect, it } from "vitest";
import {
  ARXIV_ID_RE,
  DOI_RE,
  mintPaperId,
  validatePaperRef,
} from "../../src/shared/paper_ref.js";

describe("ARXIV_ID_RE", () => {
  it("accepts canonical 2007+ ids", () => {
    expect(ARXIV_ID_RE.test("2108.12419")).toBe(true);
    expect(ARXIV_ID_RE.test("2108.12419v3")).toBe(true);
    expect(ARXIV_ID_RE.test("1503.01598")).toBe(true);
    expect(ARXIV_ID_RE.test("0908.1234")).toBe(true);
  });

  it("accepts pre-2007 category/NNNNNNN ids", () => {
    expect(ARXIV_ID_RE.test("math/0608123")).toBe(true);
    expect(ARXIV_ID_RE.test("hep-th/9901001")).toBe(true);
    expect(ARXIV_ID_RE.test("cs.CL/0512049")).toBe(true);
  });

  it("rejects malformed ids", () => {
    expect(ARXIV_ID_RE.test("not-an-id")).toBe(false);
    expect(ARXIV_ID_RE.test("21.12345")).toBe(false);          // too few year digits
    expect(ARXIV_ID_RE.test("2108.123")).toBe(false);          // too few suffix digits
    expect(ARXIV_ID_RE.test("2108.1234567")).toBe(false);      // too many suffix digits
    expect(ARXIV_ID_RE.test("arXiv:2108.12419")).toBe(false);  // includes scheme prefix
  });
});

describe("DOI_RE", () => {
  it("accepts well-formed DOIs", () => {
    expect(DOI_RE.test("10.1214/14-STS499")).toBe(true);
    expect(DOI_RE.test("10.3982/ECTA10817")).toBe(true);
    expect(DOI_RE.test("10.1093/biomet/asy016")).toBe(true);
  });

  it("rejects malformed DOIs", () => {
    expect(DOI_RE.test("not-a-doi")).toBe(false);
    expect(DOI_RE.test("10.1093")).toBe(false);             // missing slash + suffix
    expect(DOI_RE.test("11.1234/abc")).toBe(false);         // doesn't start with 10.
  });
});

describe("validatePaperRef", () => {
  it("accepts a paper with valid arxiv_id", () => {
    const r = validatePaperRef({
      title: "Intersection bounds: estimation and inference",
      authors: ["Chernozhukov", "Lee", "Rosen"],
      year: 2013,
      arxiv_id: "0907.3503",
      rationale: "tight inference for bounded-outcome intersection bounds",
    });
    expect(r).not.toBeNull();
    expect(r!.title).toBe("Intersection bounds: estimation and inference");
    expect(r!.arxiv_id).toBe("0907.3503");
    expect(r!.year).toBe(2013);
  });

  it("accepts a paper with valid doi but no arxiv", () => {
    const r = validatePaperRef({
      title: "Nonparametric bounds and sensitivity analysis of treatment effects",
      year: 2014,
      doi: "10.1214/14-STS499",
      rationale: "extends Manski bounds with sensitivity tooling",
    });
    expect(r).not.toBeNull();
    expect(r!.doi).toBe("10.1214/14-STS499");
    expect(r!.arxiv_id).toBeUndefined();
  });

  it("rejects a paper with NEITHER arxiv_id nor doi", () => {
    expect(
      validatePaperRef({
        title: "Some paper without identifiers",
        year: 2020,
        rationale: "no way to verify",
      }),
    ).toBeNull();
  });

  it("rejects a paper with malformed arxiv_id and no doi", () => {
    expect(
      validatePaperRef({
        title: "Bad id paper",
        year: 2020,
        arxiv_id: "totally-not-arxiv",
        rationale: "x",
      }),
    ).toBeNull();
  });

  it("rejects empty/missing title", () => {
    expect(
      validatePaperRef({
        title: "",
        arxiv_id: "2108.12419",
        rationale: "x",
      }),
    ).toBeNull();
    expect(validatePaperRef({})).toBeNull();
    expect(validatePaperRef(null)).toBeNull();
    expect(validatePaperRef(undefined)).toBeNull();
  });

  it("trims title whitespace", () => {
    const r = validatePaperRef({
      title: "   Spacey Title   ",
      arxiv_id: "2108.12419",
      rationale: "x",
    });
    expect(r!.title).toBe("Spacey Title");
  });

  it("defaults rationale to empty string when missing", () => {
    const r = validatePaperRef({
      title: "X",
      arxiv_id: "2108.12419",
    });
    expect(r!.rationale).toBe("");
  });
});

describe("mintPaperId", () => {
  it("prefers arxiv id (stripping vN suffix)", () => {
    expect(mintPaperId({ title: "X", arxiv_id: "2108.12419v3", rationale: "" })).toBe("2108.12419");
    expect(mintPaperId({ title: "X", arxiv_id: "math/0608123", rationale: "" })).toBe("math/0608123");
  });

  it("falls back to a DOI-derived slug", () => {
    // why: include the DOI registrant to avoid collisions across registrants with the same suffix.
    expect(mintPaperId({ title: "X", doi: "10.1214/14-STS499", rationale: "" })).toBe("10-1214-14-sts499");
    expect(mintPaperId({ title: "X", doi: "10.3982/ECTA10817", rationale: "" })).toBe("10-3982-ecta10817");
  });

  it("falls back to author-year-titleslug when neither id present (validateResolvingPaper would already reject — defensive)", () => {
    const id = mintPaperId({
      title: "Some Long Paper Title About Bounds And Inference",
      authors: ["Charles F. Manski"],
      year: 1990,
      rationale: "",
    });
    expect(id).toMatch(/^manski-1990-/);
  });

  it("two distinct OQs returning the same arxiv id mint the same paper_id (dedup-safe)", () => {
    const id1 = mintPaperId({ title: "X", arxiv_id: "0907.3503", rationale: "" });
    const id2 = mintPaperId({ title: "Y differently described", arxiv_id: "0907.3503", rationale: "" });
    expect(id1).toBe(id2);
  });
});
