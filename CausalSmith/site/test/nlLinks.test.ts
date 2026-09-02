import { describe, expect, it } from "vitest";
import {
  applyNlLinks,
  findBlockInner,
  blockDigest,
  mathBoundaryViolations,
  parseNlLinks,
  rowToken,
  segmentToken,
  validateBlocks,
  type NlBlock,
} from "../src/lib/nlLinks.js";

const block = (objId: string, inner: string) =>
  `<div class="formal-block" id="obj-${objId}" data-objid="${objId}" tabindex="0">${inner}</div>`;

const P = "nl-links-v3";

/** A block whose segments are located by substring — the TEST computes the
 *  offsets the pipeline would emit, so the assertions stay readable. */
/** The elements open at `pos`, computed the crude way a fixture can afford. */
const pathAt = (inner: string, pos: number): string[] => {
  const stack: string[] = [];
  for (const m of inner.slice(0, pos).matchAll(/<(\/?)([a-z][a-z0-9-]*)[^>]*?(\/?)>/gi)) {
    const [, closing, name, selfClose] = m;
    if (selfClose || /^(br|img|hr|input|wbr)$/i.test(name)) continue;
    if (closing) {
      const i = stack.lastIndexOf(name.toLowerCase());
      if (i >= 0) stack.splice(i, 1);
    } else stack.push(name.toLowerCase());
  }
  return stack;
};

const at = (inner: string, text: string, id: string, kind: "text" | "display" = "text") => {
  const start = inner.indexOf(text);
  if (start < 0) throw new Error(`fixture: ${JSON.stringify(text)} not in inner HTML`);
  return { id, kind, start, end: start + text.length, openPath: pathAt(inner, start) };
};

/** Fills the gaps between the named segments so the list TILES the block, the
 *  way the producer emits it. Filler segments are unassigned, so nothing wraps
 *  them; they exist only to satisfy the contract. */
const tile = (inner: string, named: NlBlock["segments"]): NlBlock["segments"] => {
  const sorted = [...named].sort((a, b) => a.start - b.start);
  const out: NlBlock["segments"] = [];
  let cursor = 0;
  let n = 0;
  const filler = (start: number, end: number) => {
    if (end > start) out.push({ id: `_f${n++}`, kind: "text", start, end, openPath: pathAt(inner, start) });
  };
  for (const seg of sorted) {
    filler(cursor, seg.start);
    out.push(seg);
    cursor = seg.end;
  }
  filler(cursor, inner.length);
  return out;
};

/** A contract-complete block over `inner`: digest, byte length, tiled segments,
 *  and the `structured`/`rowless` pair the contract requires. */
const mk = (inner: string, over: Partial<NlBlock> = {}): NlBlock => {
  const structured = over.structured ?? null;
  const block: NlBlock = {
    structured,
    segments: over.segments ? tile(inner, over.segments) : [],
    assignments: [],
    displayLinks: [],
    digest: blockDigest(inner),
    byteLength: inner.length,
  };
  if (!structured) block.rowless = true;
  return { ...block, ...over, segments: block.segments, structured };
};

describe("parseNlLinks", () => {
  const INNER = "<p>x</p>";
  const good = {
    commit: "abc123",
    policy: P,
    qid: "stat_demo",
    spec: "v1",
    blocks: {
      "T-1": {
        digest: blockDigest(INNER),
        byteLength: INNER.length,
        structured: {
          sharedHyps: [{ chip: "hyp", code: "0 < n", id: "h1" }],
          conclusions: [{ hyps: [], code: "P n", id: "c1" }],
        },
        segments: [
          { id: "s1", kind: "text", start: 0, end: 4, openPath: [] },
          { id: "s2", kind: "text", start: 4, end: INNER.length, openPath: [] },
        ],
        assignments: [{ row: "h1", segments: ["s1"] }, { row: "c1", unstated: true }],
        displayLinks: [],
      },
    },
  };
  const bound = { commit: "abc123", qid: "stat_demo", spec: "v1" };
  /** `good` with T-1's block field(s) overridden. */
  const withBlock = (over: Record<string, unknown>) => ({
    ...good,
    blocks: { "T-1": { ...good.blocks["T-1"], ...over } },
  });
  const reasonFor = (over: Record<string, unknown>) => parseNlLinks(withBlock(over))!.dropped[0]?.reason;

  it("accepts a well-formed artifact bound to this bundle", () => {
    const t = parseNlLinks(good, bound)!;
    const b = t.blocks["T-1"];
    expect(b.structured!.sharedHyps[0].id).toBe("h1");
    expect(b.digest).toBe(blockDigest(INNER));
    expect(b.assignments[1]).toEqual({ row: "c1", segments: [], unstated: true });
    expect(t.dropped).toEqual([]);
  });

  it("returns null for anything unrecognisable", () => {
    for (const bad of [null, undefined, 42, "nope", {}, { policy: P }, { policy: P, blocks: [] }]) {
      expect(parseNlLinks(bad), JSON.stringify(bad)).toBeNull();
    }
  });

  // `blocks` is the only container. A `links` key is the v2 shape.
  it("does not accept `links` as a container", () => {
    const { blocks, ...rest } = good;
    expect(parseNlLinks({ ...rest, links: blocks }, bound)).toBeNull();
  });

  it("rejects an earlier policy", () => {
    for (const policy of ["nl-links-v1", "nl-links-v2", undefined]) {
      expect(parseNlLinks({ ...good, policy }, bound), String(policy)).toBeNull();
    }
  });

  it("rejects an artifact written for another commit or another paper", () => {
    expect(parseNlLinks(good, { ...bound, commit: "def456" })).toBeNull();
    expect(parseNlLinks(good, { ...bound, qid: "stat_other" })).toBeNull();
    expect(parseNlLinks(good, { ...bound, spec: "v2" })).toBeNull();
  });

  it("skips the binding checks when the caller supplies none", () => {
    expect(parseNlLinks(good)).not.toBeNull();
  });

  // The artifact claims to account for the WHOLE block, so the contract is
  // checked in full rather than salvaged in part: half-consuming it would leave
  // rows silently untokened, which a reader cannot tell from a paper that
  // genuinely says nothing about them.
  describe("closed-world totality", () => {
    it("requires a digest and a byte length", () => {
      expect(reasonFor({ digest: undefined })).toBe("block carries no digest");
      expect(reasonFor({ byteLength: undefined })).toBe("block carries no byteLength");
    });

    it("requires an openPath on every segment", () => {
      expect(reasonFor({ segments: [{ id: "s1", kind: "text", start: 0, end: 4 }] })).toBe(
        'segment "s1" has no openPath',
      );
    });

    it("does not default an absent list", () => {
      for (const field of ["segments", "assignments", "displayLinks"]) {
        expect(reasonFor({ [field]: undefined }), field).toBe(`\`${field}\` is missing or not an array`);
      }
    });

    it("requires every row to be accounted for", () => {
      expect(reasonFor({ assignments: [{ row: "h1", segments: ["s1"] }] })).toBe(
        'row "c1" is not accounted for (assign it or mark the block rowless)',
      );
    });

    // `rowless` says "no rows to assign", so it and a statement tree exclude
    // each other; neither may be omitted silently.
    it("accepts a rowless block with no statement tree", () => {
      const t = parseNlLinks(withBlock({ rowless: true, structured: null, assignments: [] }))!;
      expect(t.dropped).toEqual([]);
      expect(t.blocks["T-1"].rowless).toBe(true);
    });

    it("rejects a rowless block that still carries assignments or a tree", () => {
      expect(reasonFor({ rowless: true, structured: null })).toBe("block is `rowless` but carries assignments");
      expect(reasonFor({ rowless: true, assignments: [] })).toBe("block is `rowless` but carries a structured tree");
    });

    it("rejects a block with neither a tree nor the rowless flag", () => {
      expect(reasonFor({ structured: null, assignments: [] })).toBe(
        "block has no `structured` tree and is not marked rowless",
      );
    });

    it("rejects a row assigned twice", () => {
      expect(
        reasonFor({
          assignments: [
            { row: "h1", segments: ["s1"] },
            { row: "h1", segments: ["s1"] },
            { row: "c1", unstated: true },
          ],
        }),
      ).toBe('row "h1" is assigned more than once');
    });

    it("rejects an invented row or segment id", () => {
      expect(reasonFor({ assignments: [{ row: "ghost", segments: ["s1"] }] })).toBe(
        'assignment names unknown row "ghost"',
      );
      expect(
        reasonFor({ assignments: [{ row: "h1", segments: ["nope"] }, { row: "c1", unstated: true }] }),
      ).toBe('assignment for "h1" names unknown segment "nope"');
    });

    it("rejects duplicate ids", () => {
      expect(
        reasonFor({
          segments: [
            { id: "s1", kind: "text", start: 0, end: 2, openPath: [] },
            { id: "s1", kind: "text", start: 2, end: 4, openPath: [] },
          ],
        }),
      ).toBe('duplicate segment id "s1"');
      expect(
        reasonFor({
          structured: {
            sharedHyps: [{ chip: "hyp", code: "a", id: "h1" }],
            conclusions: [{ hyps: [], code: "b", id: "h1" }],
          },
        }),
      ).toBe('duplicate row id "h1"');
    });

    // `unstated` is how "the paper does not state this" is said, and the
    // difference from "stated, somewhere unspecified" matters to the reader.
    it("rejects a stated row with no segments", () => {
      expect(
        reasonFor({ assignments: [{ row: "h1", segments: [] }, { row: "c1", unstated: true }] }),
      ).toBe('row "h1" is stated but has no segments (use unstated)');
    });

    it("rejects a content-bearing row with no id", () => {
      expect(
        reasonFor({
          structured: { sharedHyps: [{ chip: "hyp", code: "a" }], conclusions: [{ hyps: [], code: "b", id: "c1" }] },
        }),
      ).toBe("a content-bearing row in `structured` has no id");
    });

    // A card that only BRANCHES renders nothing of its own — it is a bracket
    // around its children — so it carries no id, is not assignable, and must
    // not be counted as an unaccounted-for row.
    it("accepts a purely branching card with no id", () => {
      const t = parseNlLinks(
        withBlock({
          structured: {
            sharedHyps: [],
            conclusions: [
              { hyps: [], sub: [{ hyps: [], code: "P", id: "c1" }, { hyps: [], code: "Q", id: "c2" }] },
            ],
          },
          assignments: [{ row: "c1", segments: ["s1"] }, { row: "c2", unstated: true }],
        }),
      )!;
      expect(t.dropped).toEqual([]);
      expect(t.blocks["T-1"].structured!.conclusions[0].id).toBeUndefined();
      expect(t.blocks["T-1"].structured!.conclusions[0].sub).toHaveLength(2);
    });

    it("still requires an id on a branching card that carries an intro", () => {
      expect(
        reasonFor({
          structured: {
            sharedHyps: [],
            conclusions: [{ hyps: [], intro: "∃ k,", sub: [{ hyps: [], code: "P", id: "c1" }] }],
          },
          assignments: [{ row: "c1", segments: ["s1"] }],
        }),
      ).toBe("a content-bearing row in `structured` has no id");
    });

    it("rejects an id that is empty or contains whitespace", () => {
      expect(reasonFor({ segments: [{ id: "a b", kind: "text", start: 0, end: 8, openPath: [] }] })).toBe(
        "a segment has no id, or its id contains whitespace",
      );
    });

    // An empty list tiles an empty block and nothing else: total coverage of
    // prose while addressing none of it is the one claim it must not make.
    it("rejects a block with prose but no segments at all", () => {
      expect(reasonFor({ segments: [] })).toBe("block has 8 bytes but no segments");
    });

    // Each of these says something the other contradicts.
    it("rejects a row that is both unstated and placed", () => {
      expect(
        reasonFor({ assignments: [{ row: "h1", unstated: true, segments: ["s1"] }, { row: "c1", unstated: true }] }),
      ).toBe('row "h1" is marked unstated but also carries segments');
    });

    it("rejects a display formula that is both a decl and presentation-only", () => {
      const seg = { id: "d1", kind: "display", start: 0, end: 8, openPath: [] };
      expect(
        reasonFor({
          segments: [seg],
          assignments: [{ row: "h1", segments: ["d1"] }, { row: "c1", unstated: true }],
          displayLinks: [{ segment: "d1", decl: "Demo.foo", presentationOnly: true }],
        }),
      ).toBe('displayLink for "d1" is both a decl and presentationOnly');
    });

    // The producer schema permits these only as literal `true`. Reading `false`
    // as a soft "no" would silently accept a shape it never emits, and turn a
    // producer bug into a quietly wrong page.
    it("rejects a discriminator that is present but not literal true", () => {
      expect(
        reasonFor({ assignments: [{ row: "h1", segments: ["s1"], unstated: false }, { row: "c1", unstated: true }] }),
      ).toBe("`unstated` is present but not literal true");
      const seg = { id: "d1", kind: "display", start: 0, end: INNER.length, openPath: [] };
      expect(
        reasonFor({
          segments: [seg],
          assignments: [{ row: "h1", segments: ["d1"] }, { row: "c1", unstated: true }],
          displayLinks: [{ segment: "d1", decl: "Demo.foo", presentationOnly: false }],
        }),
      ).toBe("`presentationOnly` is present but not literal true");
    });

    it("rejects a string field that is present with a non-string value", () => {
      expect(reasonFor({ digest: 42 })).toBe("`digest` is present but not a string");
      expect(reasonFor({ segments: [{ id: 7, kind: "text", start: 0, end: 8, openPath: [] }] })).toBe(
        "a segment's id is present but not a string",
      );
      expect(
        reasonFor({ assignments: [{ row: 7, segments: ["s1"] }, { row: "c1", unstated: true }] }),
      ).toBe("an assignment's row is present but not a string");
      expect(
        reasonFor({ displayLinks: [{ segment: "s1", decl: 7 }] }),
      ).toBe("a displayLink's decl is present but not a string");
      // Inside the tree the whole parse is refused rather than half-read.
      expect(
        reasonFor({
          structured: { sharedHyps: [{ chip: "hyp", code: "a", id: 7 }], conclusions: [{ hyps: [], code: "b", id: "c1" }] },
        }),
      ).toBe("`structured` is not a readable statement tree");
    });

    // The producer tiles the block end to end; a hole means a segment was lost.
    it("rejects segments that do not tile the block", () => {
      const seg = (id: string, start: number, end: number) => ({ id, kind: "text", start, end, openPath: [] });
      expect(reasonFor({ segments: [seg("s1", 2, 8)] })).toBe("segments start at 2, not 0");
      expect(reasonFor({ segments: [seg("s1", 0, 3), seg("s2", 4, 8)] })).toContain("do not tile");
      expect(reasonFor({ segments: [seg("s1", 0, 4)] })).toBe("segments end at 4, not the block's 8 bytes");
    });

    it("requires every display segment to be accounted for", () => {
      const seg = { id: "d1", kind: "display", start: 0, end: INNER.length, openPath: [] };
      expect(reasonFor({ segments: [seg], assignments: [{ row: "h1", segments: ["d1"] }, { row: "c1", unstated: true }] })).toBe(
        'display segment "d1" is not accounted for in displayLinks',
      );
    });

    // A display can show several constants at once, so several decl entries
    // may share a segment — but exposition and Lean exclude each other, and
    // "exposition" is said exactly once.
    it("accepts several decls on one display segment", () => {
      const seg = { id: "d1", kind: "display", start: 0, end: INNER.length, openPath: [] };
      const t = parseNlLinks(
        withBlock({
          segments: [seg],
          assignments: [{ row: "h1", segments: ["d1"] }, { row: "c1", unstated: true }],
          displayLinks: [{ segment: "d1", decl: "A" }, { segment: "d1", decl: "B" }],
        }),
      )!;
      expect(t.dropped).toEqual([]);
      expect(t.blocks["T-1"].displayLinks.map((d) => d.decl)).toEqual(["A", "B"]);
    });

    it("rejects a display segment that is both linked and presentation-only", () => {
      const seg = { id: "d1", kind: "display", start: 0, end: INNER.length, openPath: [] };
      const base = {
        segments: [seg],
        assignments: [{ row: "h1", segments: ["d1"] }, { row: "c1", unstated: true }],
      };
      expect(
        reasonFor({ ...base, displayLinks: [{ segment: "d1", decl: "A" }, { segment: "d1", presentationOnly: true }] }),
      ).toBe('display segment "d1" is both linked to decls and marked presentationOnly');
      expect(
        reasonFor({
          ...base,
          displayLinks: [{ segment: "d1", presentationOnly: true }, { segment: "d1", presentationOnly: true }],
        }),
      ).toBe('display segment "d1" is marked presentationOnly twice');
    });

    it("rejects a displayLink on a text segment, or naming nothing", () => {
      expect(reasonFor({ displayLinks: [{ segment: "s1", decl: "A" }] })).toBe(
        'displayLink targets non-display segment "s1"',
      );
      const seg = { id: "d1", kind: "display", start: 0, end: INNER.length, openPath: [] };
      expect(
        reasonFor({
          segments: [seg],
          assignments: [{ row: "h1", segments: ["d1"] }, { row: "c1", unstated: true }],
          displayLinks: [{ segment: "d1" }],
        }),
      ).toBe('displayLink for "d1" has neither a decl nor presentationOnly');
    });

    it("rejects an unreadable statement tree, but allows an explicitly absent one", () => {
      expect(reasonFor({ structured: { sharedHyps: [{ chip: "wat", code: "x" }], conclusions: [] } })).toBe(
        "`structured` is not a readable statement tree",
      );
      const t = parseNlLinks(withBlock({ structured: null, assignments: [], rowless: true }))!;
      expect(t.dropped).toEqual([]);
      expect(t.blocks["T-1"].structured).toBeNull();
    });

    // The renderer relies on it, so an artifact that breaks it is malformed.
    it("requires exactly one of code / sub on every card", () => {
      const withCard = (card: unknown) =>
        reasonFor({ structured: { sharedHyps: [], conclusions: [card] }, assignments: [] });
      expect(withCard({ hyps: [], code: "a", sub: [{ hyps: [], code: "b", id: "x" }], id: "c" })).toBeTruthy();
      expect(withCard({ hyps: [], id: "c" })).toBeTruthy();
    });
  });
});

describe("findBlockInner", () => {
  it("returns the inner range, past nested same-name elements", () => {
    const html = `<p>before</p>${block("T-1", "<div>nested</div>tail")}<p>after</p>`;
    const r = findBlockInner(html, "T-1")!;
    expect(html.slice(r.start, r.end)).toBe("<div>nested</div>tail");
  });

  it("is not fooled by a `>` inside an attribute value", () => {
    const html = `<div class="formal-block" title="a > b" data-objid="T-1">inner</div>`;
    const r = findBlockInner(html, "T-1")!;
    expect(html.slice(r.start, r.end)).toBe("inner");
  });

  // `data-objid` is not unique: a `leanref` cross-reference appears in the prose
  // BEFORE the block it points at, and offsets are measured against the block.
  it("skips an inline leanref reference and finds the formal block", () => {
    const html =
      `<p>see <span class="leanref" data-objid="T-1">Theorem 1</span> below</p>` +
      block("T-1", "<p>the real body</p>");
    const r = findBlockInner(html, "T-1")!;
    expect(html.slice(r.start, r.end)).toBe("<p>the real body</p>");
  });

  it("returns null for an unknown obj_id, an unclosed block, or a non-block match", () => {
    expect(findBlockInner(block("T-1", "x"), "T-2")).toBeNull();
    expect(findBlockInner(`<div class="formal-block" data-objid="T-1">oops`, "T-1")).toBeNull();
    expect(findBlockInner(`<span class="leanref" data-objid="T-1">x</span>`, "T-1")).toBeNull();
  });
});

describe("validateBlocks", () => {
  const INNER = "<p>the estimator is bounded</p>";
  const HTML = block("T-1", INNER);
  const check = (over: Partial<NlBlock>) => validateBlocks(HTML, { "T-1": mk(INNER, over) });

  it("passes a block whose offsets and digest match the body", () => {
    const r = check({ segments: [at(INNER, "the estimator", "s1")] });
    expect(r.problems).toEqual([]);
    expect(Object.keys(r.blocks)).toEqual(["T-1"]);
  });

  // The offsets index bytes that are no longer there; applying them anyway
  // would highlight arbitrary text.
  it("refuses a block whose HTML has changed since it was written", () => {
    const r = validateBlocks(HTML, {
      "T-1": { ...mk(INNER, { segments: [at(INNER, "the estimator", "s1")] }), digest: blockDigest("something else") },
    });
    expect(r.blocks).toEqual({});
    expect(r.problems[0].reason).toContain("block HTML has changed");
  });

  // The digest collapses whitespace, so a pure reflow leaves it equal while
  // moving every offset. The exact length catches that.
  it("refuses a block whose HTML is a different length", () => {
    const longer = INNER.replace("the estimator", "the  estimator"); // +1 byte
    const r = validateBlocks(block("T-1", longer), {
      "T-1": mk(INNER, { segments: [at(INNER, "the estimator", "s1")] }),
    });
    expect(r.blocks).toEqual({});
    // The length is the cheap pre-check, so it names the discrepancy first.
    expect(r.problems[0].reason).toContain("bytes, not the");
  });

  it("refuses a block that is not in the body at all", () => {
    const r = validateBlocks(HTML, { GONE: mk("x") });
    expect(r.problems).toEqual([{ objId: "GONE", reason: "no such block in the body" }]);
  });

  it("refuses a block whose obj_id is not a single token", () => {
    expect(validateBlocks(HTML, { "sym:\\mathcal C": mk("x") }).problems[0].reason).toBe(
      "obj_id is not a single token",
    );
  });

  it("refuses out-of-bounds, inverted and empty ranges", () => {
    for (const seg of [
      { id: "s1", kind: "text" as const, start: 3, end: 9999, openPath: [] },
      { id: "s1", kind: "text" as const, start: 7, end: 3, openPath: [] },
      { id: "s1", kind: "text" as const, start: 4, end: 4, openPath: [] },
    ]) {
      expect(check({ segments: [seg] }).problems[0].reason).toContain("out of bounds");
    }
  });

  it("refuses a boundary inside a tag", () => {
    const inTag = INNER.indexOf("<p>") + 1;
    expect(check({ segments: [{ id: "s1", kind: "text", start: inTag, end: inTag + 6, openPath: [] }] }).problems[0].reason).toContain(
      "inside a tag",
    );
  });

  it("refuses overlapping segments", () => {
    const r = check({ segments: [at(INNER, "the estimator", "s1"), at(INNER, "estimator is", "s2")] });
    expect(r.problems[0].reason).toContain("overlap");
  });

  // Segments are NOT required to balance their own tags: pandoc wraps every
  // sentence in a `<p>`, so demanding balance left almost nothing addressable.
  // The artifact declares what is open where a segment starts, and that claim
  // is checked against the real markup.
  it("accepts a segment that starts inside an open element", () => {
    const inner = "<p>alpha</p><p>beta</p>";
    const html = block("T-1", inner);
    const seg = at(inner, "alpha</p><p>beta", "s1");
    expect(seg.openPath).toEqual(["p"]);
    expect(validateBlocks(html, { "T-1": mk(inner, { segments: [seg] }) }).problems).toEqual([]);
  });

  it("refuses a segment whose openPath does not match the markup", () => {
    const inner = "<p>alpha</p>";
    const r = validateBlocks(block("T-1", inner), {
      "T-1": mk(inner, { segments: [{ ...at(inner, "alpha", "s1"), openPath: ["div", "em"] }] }),
    });
    expect(r.blocks).toEqual({});
    expect(r.problems[0].reason).toContain("claims openPath [div, em] but sits inside [p]");
  });

  describe("formulas", () => {
    const MATH = '<span class="math inline">\\(x&gt;0\\)</span>';
    const DISPLAY = '<span class="math display">\\[y=1\\]</span>';
    const INNER2 = `<p>given ${MATH} we win</p>${DISPLAY}`;
    const HTML2 = block("T-1", INNER2);
    const check2 = (over: Partial<NlBlock>) => validateBlocks(HTML2, { "T-1": mk(INNER2, over) });

    // KaTeX re-renders each formula from its raw TeX with a non-greedy
    // `</span>` match, so a boundary inside one truncates the formula and the
    // span vanishes from the rendered page.
    it("refuses a boundary inside a formula", () => {
      const start = INNER2.indexOf("\\(x");
      expect(check2({ segments: [{ id: "s1", kind: "text", start, end: start + 4, openPath: ["p"] }] }).problems[0].reason).toContain(
        "inside a formula",
      );
    });

    it("accepts a text segment containing a whole inline formula", () => {
      expect(check2({ segments: [at(INNER2, `given ${MATH} we win`, "s1")] }).problems).toEqual([]);
    });

    it("requires a display segment to BE a display formula", () => {
      const linked = { displayLinks: [{ segment: "d1", decl: "A" }] };
      expect(check2({ segments: [at(INNER2, "we win", "d1", "display")], ...linked }).problems[0].reason).toContain(
        "is not a math element",
      );
      expect(check2({ segments: [at(INNER2, MATH, "d1", "display")], ...linked }).problems[0].reason).toContain(
        "the formula is inline",
      );
      expect(check2({ segments: [at(INNER2, DISPLAY, "d1", "display")], ...linked }).problems).toEqual([]);
    });
  });
});

describe("applyNlLinks", () => {
  const INNER = "<p>the estimator is bounded</p>";
  const HTML = block("T-1", INNER);

  it("wraps an assigned segment with the rows it states", () => {
    const { html, skipped } = applyNlLinks(HTML, {
      "T-1": mk(INNER, {
        segments: [at(INNER, "the estimator", "s1")],
        assignments: [{ row: "h1", segments: ["s1"] }],
      }),
    });
    expect(skipped).toEqual([]);
    expect(html).toBe(block("T-1", '<p><span data-xl="T-1#h1">the estimator</span> is bounded</p>'));
  });

  it("lists every row a segment states, in one token list", () => {
    const { html } = applyNlLinks(HTML, {
      "T-1": mk(INNER, {
        segments: [at(INNER, "the estimator", "s1")],
        assignments: [{ row: "h1", segments: ["s1"] }, { row: "h2", segments: ["s1"] }],
      }),
    });
    expect(html).toContain('data-xl="T-1#h1 T-1#h2"');
  });

  it("wraps one row's several segments, each carrying that row's token", () => {
    const { html } = applyNlLinks(HTML, {
      "T-1": mk(INNER, {
        segments: [at(INNER, "the estimator", "s1"), at(INNER, "bounded", "s2")],
        assignments: [{ row: "h1", segments: ["s1", "s2"] }],
      }),
    });
    expect(html).toBe(
      block("T-1", '<p><span data-xl="T-1#h1">the estimator</span> is <span data-xl="T-1#h1">bounded</span></p>'),
    );
  });

  it("leaves an unassigned segment alone, and an unstated row unwrapped", () => {
    const { html } = applyNlLinks(HTML, {
      "T-1": mk(INNER, {
        segments: [at(INNER, "the estimator", "s1")],
        assignments: [{ row: "c1", segments: [], unstated: true }],
      }),
    });
    expect(html).toBe(HTML);
  });

  // A segment may begin inside a `<p>` and end outside it. One span around the
  // whole range would be malformed, so the range is chopped at tag boundaries
  // and each text run gets its own span carrying the same tokens.
  describe("run splitting", () => {
    it("wraps each text run of a segment that crosses a paragraph break", () => {
      const inner = "<p>alpha beta</p><p>gamma delta</p>";
      const seg = at(inner, "beta</p><p>gamma", "s1");
      const { html, skipped } = applyNlLinks(block("T-1", inner), {
        "T-1": mk(inner, { segments: [seg], assignments: [{ row: "h1", segments: ["s1"] }] }),
      });
      expect(skipped).toEqual([]);
      expect(html).toBe(
        block(
          "T-1",
          '<p>alpha <span data-xl="T-1#h1">beta</span></p>' +
            '<p><span data-xl="T-1#h1">gamma</span> delta</p>',
        ),
      );
    });

    it("splits at an inline element without interleaving", () => {
      const inner = "<p>a <em>b</em> c</p>";
      const seg = at(inner, "a <em>b</em> c", "s1");
      const { html } = applyNlLinks(block("T-1", inner), {
        "T-1": mk(inner, { segments: [seg], assignments: [{ row: "h1", segments: ["s1"] }] }),
      });
      expect(html).toBe(
        block(
          "T-1",
          '<p><span data-xl="T-1#h1">a </span><em><span data-xl="T-1#h1">b</span></em>' +
            '<span data-xl="T-1#h1"> c</span></p>',
        ),
      );
    });

    it("wraps a segment that starts inside an element and ends after it", () => {
      const inner = "<p>alpha</p>tail";
      const seg = at(inner, "alpha</p>tail", "s1");
      const { html } = applyNlLinks(block("T-1", inner), {
        "T-1": mk(inner, { segments: [seg], assignments: [{ row: "h1", segments: ["s1"] }] }),
      });
      expect(html).toBe(
        block("T-1", '<p><span data-xl="T-1#h1">alpha</span></p><span data-xl="T-1#h1">tail</span>'),
      );
    });

    // A formula travels as one atom: KaTeX re-renders it from raw TeX, so its
    // own tags must never become split points.
    it("never splits inside a formula", () => {
      const MATH = '<span class="math inline">\\(x&gt;0\\)</span>';
      const inner = `<p>given ${MATH} we win</p>`;
      const seg = at(inner, `given ${MATH} we win`, "s1");
      const { html } = applyNlLinks(block("T-1", inner), {
        "T-1": mk(inner, { segments: [seg], assignments: [{ row: "h1", segments: ["s1"] }] }),
      });
      expect(html).toContain(`<span data-xl="T-1#h1">given ${MATH} we win</span>`);
      expect(mathBoundaryViolations(html)).toBe(0);
    });
  });

  it("changes nothing when there are no blocks", () => {
    expect(applyNlLinks(HTML, {}).html).toBe(HTML);
  });

  it("keeps adjacent spans properly nested, not interleaved", () => {
    const inner = "<p>alphabeta</p>";
    const { html } = applyNlLinks(block("T-1", inner), {
      "T-1": mk(inner, {
        segments: [at(inner, "alpha", "s1"), at(inner, "beta", "s2")],
        assignments: [{ row: "h1", segments: ["s1"] }, { row: "h2", segments: ["s2"] }],
      }),
    });
    expect(html).toContain('<span data-xl="T-1#h1">alpha</span><span data-xl="T-1#h2">beta</span>');
  });

  it("escapes what it writes into attributes", () => {
    const { html } = applyNlLinks(HTML, {
      "T-1": mk(INNER, {
        segments: [{ ...at(INNER, "the estimator", "d1"), kind: "display" as const }],
        displayLinks: [{ segment: "d1", decl: 'a"b&c' }],
      }),
    });
    expect(html).toContain('data-xl-decl="a&quot;b&amp;c"');
  });

  it("is deterministic across obj_id iteration order", () => {
    const inner = "<p>one</p>";
    const html = block("A", inner) + block("B", inner);
    const one = mk(inner, {
      segments: [at(inner, "one", "s")],
      assignments: [{ row: "r", segments: ["s"] }],
    });
    expect(applyNlLinks(html, { A: one, B: one }).html).toBe(applyNlLinks(html, { B: one, A: one }).html);
  });

  describe("display links are two-sided", () => {
    const DISPLAY = '<span class="math display">\\[y=1\\]</span>';
    const INNER2 = `<p>see</p>${DISPLAY}`;
    const HTML2 = block("T-1", INNER2);
    const seg = () => at(INNER2, DISPLAY, "d1", "display");

    // `data-xl-decl` alone points one way. The segment's own token is what the
    // component carries too, so hovering either side lights the other.
    it("mints a segment token on the prose as well as naming the decl", () => {
      const { html, skipped } = applyNlLinks(HTML2, {
        "T-1": mk(INNER2, { segments: [seg()], displayLinks: [{ segment: "d1", decl: "Demo.thing" }] }),
      });
      expect(skipped).toEqual([]);
      expect(html).toContain(`<span data-xl="T-1#d1" data-xl-decl="Demo.thing">${DISPLAY}</span>`);
      expect(segmentToken("T-1", "d1")).toBe("T-1#d1");
      expect(mathBoundaryViolations(html)).toBe(0);
    });

    it("names every decl a formula shows, under one shared token", () => {
      const { html, skipped } = applyNlLinks(HTML2, {
        "T-1": mk(INNER2, {
          segments: [seg()],
          displayLinks: [
            { segment: "d1", decl: "Demo.alpha" },
            { segment: "d1", decl: "Demo.beta" },
          ],
        }),
      });
      expect(skipped).toEqual([]);
      // ONE token for the segment; both constants named on it.
      expect(html).toContain('<span data-xl="T-1#d1" data-xl-decl="Demo.alpha Demo.beta">');
    });

    it("carries a row token and the display token together", () => {
      const { html } = applyNlLinks(HTML2, {
        "T-1": mk(INNER2, {
          segments: [seg()],
          assignments: [{ row: "c1", segments: ["d1"] }],
          displayLinks: [{ segment: "d1", decl: "Demo.thing" }],
        }),
      });
      expect(html).toContain('data-xl="T-1#c1 T-1#d1"');
    });

    it("marks a presentation-only formula quietly, with no crosslink token", () => {
      const { html } = applyNlLinks(HTML2, {
        "T-1": mk(INNER2, { segments: [seg()], displayLinks: [{ segment: "d1", presentationOnly: true }] }),
      });
      expect(html).toContain(`<span data-xl-presentation>${DISPLAY}</span>`);
      expect(html).not.toContain("data-xl=");
    });
  });
});

describe("tokens", () => {
  it("name a row and a display segment of a block", () => {
    expect(rowToken("thm:foo", "h3")).toBe("thm:foo#h3");
    expect(segmentToken("thm:foo", "d1")).toBe("thm:foo#d1");
  });
});

describe("blockDigest", () => {
  // A RAW hash, unlike the pipeline's whitespace-insensitive `hashEnvBody`:
  // this guards byte offsets, and a reflow moves every one of them.
  it("changes when the bytes change, reflow included", () => {
    expect(blockDigest("<p>a b</p>")).not.toBe(blockDigest("<p>a\n  b</p>"));
    expect(blockDigest("<p>a b</p>")).not.toBe(blockDigest("<p>a c</p>"));
    expect(blockDigest("<p>a b</p>")).toBe(blockDigest("<p>a b</p>"));
  });
});
