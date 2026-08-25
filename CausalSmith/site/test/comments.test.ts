import { describe, expect, it } from "vitest";
import {
  makeAnchor,
  reanchor,
  segmentSentences,
  similarity,
  type SentenceRef,
} from "../src/lib/comments/anchor.js";
import { parseComment, serializeComment } from "../src/lib/comments/schema.js";

function refs(texts: string[]): SentenceRef[] {
  return texts.map((text, i) => ({ id: `b-${i}`, text }));
}

describe("segmentSentences", () => {
  it("splits ordinary scholarly prose", () => {
    const s = segmentSentences(
      "We study the ATE under weak overlap. The lower bound uses Le Cam's method. The constant is sharp.",
    );
    expect(s).toEqual([
      "We study the ATE under weak overlap.",
      "The lower bound uses Le Cam's method.",
      "The constant is sharp.",
    ]);
  });

  it("does not split after common abbreviations or initials", () => {
    const s = segmentSentences(
      "The data are i.i.d. Gaussian, cf. Section 2. See W. K. Newey for background.",
    );
    expect(s).toEqual([
      "The data are i.i.d. Gaussian, cf. Section 2.",
      "See W. K. Newey for background.",
    ]);
  });

  it("treats the QED tombstone as a sentence end", () => {
    const s = segmentSentences("Summing the contributions yields the display. ∎ Next section.");
    expect(s[0]).toBe("Summing the contributions yields the display. ∎");
  });

  it("keeps a display-equation block whole", () => {
    const eq = "inf sup E |τ̂ − τ(P)| ≥ C √(K ⁄ n) (3.1)";
    expect(segmentSentences(eq)).toEqual([eq]);
  });

  it("collapses whitespace and handles empty input", () => {
    expect(segmentSentences("  \n ")).toEqual([]);
    expect(segmentSentences("One   sentence\nonly")).toEqual(["One sentence only"]);
  });
});

describe("similarity", () => {
  it("is 1 on normalized-equal strings and 0 against empty", () => {
    expect(similarity("A  b\nc", "a b C")).toBe(1);
    expect(similarity("anything", "")).toBe(0);
  });

  it("scores a small rewording high and a rewrite low", () => {
    const orig = "The separation constant is C = 4√2, an absolute constant independent of K.";
    const reworded =
      "The separation constant may be taken as C = 4√2, an absolute constant that does not depend on K.";
    const rewritten =
      "For all K ≥ 2, every estimator incurs worst-case risk at least C √(K ⁄ (n h)) uniformly.";
    expect(similarity(orig, reworded)).toBeGreaterThan(0.7);
    expect(similarity(orig, rewritten)).toBeLessThan(0.55);
  });
});

describe("makeAnchor / reanchor", () => {
  const doc = refs([
    "We study the ATE under weak overlap.",
    "The lower bound uses Le Cam's two-point method.",
    "The separation constant is C = 4√2, an absolute constant independent of K.",
    "Summing the contributions yields the display.",
  ]);

  it("re-anchors exactly on unchanged text", () => {
    const a = makeAnchor(doc, 2, 3);
    const m = reanchor(a, doc);
    expect(m).toMatchObject({ state: "anchored", start: 2, end: 3, score: 1 });
  });

  it("survives sentences being inserted before the quote", () => {
    const a = makeAnchor(doc, 2, 3);
    const shifted = refs(["A brand new opening sentence.", ...doc.map((s) => s.text)]);
    const m = reanchor(a, shifted);
    expect(m.state).toBe("anchored");
    expect(shifted[m.start].text).toBe(doc[2].text);
  });

  it("reports drifted on a small rewording", () => {
    const a = makeAnchor(doc, 2, 3);
    const edited = doc.map((s) => ({ ...s }));
    edited[2] = {
      id: edited[2].id,
      text: "The separation constant may be taken as C = 4√2, an absolute constant that does not depend on K.",
    };
    const m = reanchor(a, edited);
    expect(m.state).toBe("drifted");
    expect(m.start).toBe(2);
    expect(m.score).toBeGreaterThan(0.55);
    expect(m.score).toBeLessThan(0.985);
  });

  it("reports archived on a full rewrite", () => {
    const a = makeAnchor(doc, 2, 3);
    const edited = doc.map((s) => ({ ...s }));
    edited[2] = {
      id: edited[2].id,
      text: "For all K ≥ 2 and n h ≥ 1, the worst-case risk is at least of order √(K ⁄ (n h)), uniformly over the class.",
    };
    const m = reanchor(a, edited);
    expect(m.state).toBe("archived");
    expect(m.start).toBe(-1);
  });

  it("uses context to disambiguate repeated sentences", () => {
    const dup = refs([
      "The proof proceeds in two steps.",
      "This is immediate.",
      "The second step is harder.",
      "This is immediate.",
      "The theorem follows.",
    ]);
    const a = makeAnchor(dup, 3, 4); // the SECOND "This is immediate."
    const m = reanchor(a, dup);
    expect(m).toMatchObject({ state: "anchored", start: 3, end: 4 });
  });

  it("re-anchors a multi-sentence quote and tolerates a merged sentence as drift", () => {
    const a = makeAnchor(doc, 1, 3);
    expect(a.count).toBe(2);
    const merged = refs([
      doc[0].text,
      "The lower bound uses Le Cam's two-point method, where the separation constant is C = 4√2, independent of K.",
      doc[3].text,
    ]);
    const m = reanchor(a, merged);
    expect(m.state).toBe("drifted");
    expect(m.start).toBe(1);
  });

  it("handles an empty document and rejects bad ranges", () => {
    const a = makeAnchor(doc, 0, 1);
    expect(reanchor(a, []).state).toBe("archived");
    expect(() => makeAnchor(doc, 2, 2)).toThrow();
    expect(() => makeAnchor(doc, -1, 1)).toThrow();
  });
});

describe("comment schema", () => {
  const anchor = {
    exact: "The separation constant is C = 4√2.",
    prefix: "two-point method.",
    suffix: "Summing the contributions",
    count: 1,
  };

  it("round-trips an anchored tagged comment", () => {
    const body = serializeComment({
      meta: { v: 1, paper: "stat_discrete_ate", tag: "verified", anchor, revision: "d2bf655f" },
      text: "Checked against the Lean declaration — constants match.",
    });
    const parsed = parseComment(body, "stat_discrete_ate");
    expect(parsed.meta.tag).toBe("verified");
    expect(parsed.meta.anchor).toEqual(anchor);
    expect(parsed.meta.revision).toBe("d2bf655f");
    expect(parsed.text).toBe("Checked against the Lean declaration — constants match.");
  });

  it("keeps the metadata header invisible-ish: body still starts with an HTML comment", () => {
    const body = serializeComment({
      meta: { v: 1, paper: "p", tag: "none" },
      text: "Plain remark.",
    });
    expect(body.startsWith("<!-- causalsmith:comment v1\n")).toBe(true);
    expect(body).toContain("\n-->\n\nPlain remark.");
  });

  it("degrades a hand-written GitHub reply to an untagged page-level comment", () => {
    const parsed = parseComment("Nice paper! Typo in (3.1).", "p");
    expect(parsed.meta.tag).toBe("none");
    expect(parsed.meta.anchor).toBeUndefined();
    expect(parsed.text).toBe("Nice paper! Typo in (3.1).");
  });

  it("degrades malformed or hostile headers without throwing", () => {
    const junk = "<!-- causalsmith:comment v1\n{not json\n-->\n\nhello";
    expect(parseComment(junk, "p").text).toBe(junk.trim());
    const badTag = serializeComment({
      meta: { v: 1, paper: "p", tag: "none" },
      text: "x",
    }).replace('"tag":"none"', '"tag":"admin"');
    expect(parseComment(badTag, "p").meta.tag).toBe("none");
    const badAnchor = "<!-- causalsmith:comment v1\n" +
      JSON.stringify({ v: 1, paper: "p", tag: "problem", anchor: { exact: "", count: 0 } }) +
      "\n-->\n\ntext";
    const p = parseComment(badAnchor, "p");
    expect(p.meta.tag).toBe("problem");
    expect(p.meta.anchor).toBeUndefined();
  });
});
