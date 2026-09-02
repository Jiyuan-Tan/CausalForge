import { describe, it, expect, vi } from "vitest";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import {
  applyVerdicts,
  assignSection,
  assignmentProblems,
  buildBlockInput,
  buildDeclIndex,
  chunkBySize,
  claimCount,
  coerceDisplayLinks,
  declIsKnown,
  declVocabularyAppendix,
  chunkClaims,
  closurePieces,
  ensureNlLinks,
  extractBlockHtml,
  isPropDefinition,
  isTheoremLike,
  leanPieces,
  leanPiecesWithClosure,
  leanPromptText,
  loadDeclIndex,
  normalizeDisplayLinks,
  rawDigest,
  resolveDeclName,
  referencedDecls,
  resolveIndexed,
  selectsForNlLinks,
  verifyCacheKey,
  verifyProblems,
  verifySection,
  verifySectionFor,
  verifyUnitProblems,
  verifyUnits,
  MAX_PROMPT_BYTES,
  MAX_VERIFY_CLAIMS,
  NL_LINKS_POLICY,
  STATEMENT_PART,
  type BlockInput,
  type IndexedLeanDecl,
  type NlLinkSelectable,
} from "../src/presentation/nl_links.js";
import { displayRanges, openStacks, segmentBlock, segmentText, segmentationProblems } from "../src/presentation/nl_segments.js";
import { hashEnvBody } from "../src/presentation/tex_anchors.js";
import { assignRowIds, structureStatementView } from "../src/presentation/lean_structure.js";
import type { LeanSnippet } from "../src/presentation/types.js";

const DISPLAY = (inner: string) => `<span class="math display">${inner}</span>`;
const INLINE = (inner: string) => `<span class="math inline">${inner}</span>`;

const BLOCK_HTML =
  '<span class="env-label">Assumption 1.</span>' +
  `<p>The propensity lies in the interval. Every cell carries positive mass ${INLINE("\\(m>0\\)")} here.</p>` +
  DISPLAY("\\[A_0 = 1\\]") +
  "<p>That constant is auxiliary.</p>";

const PAPER_BODY = [
  '<div class="formal-block kind-definition" id="obj-synth_1" data-presentation-only="true"><p>Synth.</p></div>',
  `<div class="formal-block kind-assumption" id="obj-a1" data-objid="a1" tabindex="0">${BLOCK_HTML}</div>`,
  '<p>Prose mentioning <span class="leanref" data-objid="a1">Overlap</span> inline.</p>',
].join("\n");

/** A theorem the ported parser structures into rows. */
const THEOREM = [
  "theorem overlap_bound",
  "    (eps : ℝ)",
  "    (h1 : 0 < eps)",
  "    (h2 : eps ≤ 1) :",
  "    eps ≤ 1 - eps",
].join("\n");

const SNIPPET: LeanSnippet = {
  decl: "overlap_bound",
  file: "Basic.lean",
  line: 12,
  statement: THEOREM,
  sorry_free: true,
  axioms: null,
};

const UNRELATED_INDEX = [
  { name: "Other.unrelated", kind: "def", file: "Other.lean", line: 1, source: "def unrelated : Nat := 0" },
  // A real index contains the paper's own declarations; the display-link check
  // resolves against the whole index, so the block's own decl must be in it.
  { name: "Ns.overlap_bound", kind: "theorem", file: "Basic.lean", line: 12, source: "theorem overlap_bound : True := trivial" },
];

const writeIndex = (dir: string, entries: unknown[]) =>
  writeFile(path.join(dir, "paper_library_index.json"), JSON.stringify({ entries }), "utf8");

const entry = (obj_id: string, over: Partial<NlLinkSelectable> = {}): NlLinkSelectable => ({
  obj_id,
  env: "assumptionv",
  status: "matched",
  ...over,
});

const index = () => buildDeclIndex(UNRELATED_INDEX as IndexedLeanDecl[]);
const inputFor = (over: Partial<{ html: string; snippet: LeanSnippet }> = {}): BlockInput =>
  buildBlockInput({
    objId: "a1",
    blockHtml: over.html ?? BLOCK_HTML,
    snippet: over.snippet ?? SNIPPET,
    index: index(),
  })!;

/** Ids a request actually asked about. */
const objIdsInPrompt = (prompt: string): string[] => [...prompt.matchAll(/^### (.+)$/gm)].map((m) => m[1]);

/** A total, all-negative answer — the shape both validators must accept. */
const totalAnswer = (input: BlockInput) => ({
  assignments: input.rows.map((r) => ({ row: r.id, unstated: true as const })),
  displayLinks: input.segments
    .filter((s) => s.kind === "display")
    .map((s) => ({ segment: s.id, presentationOnly: true as const })),
});

/** codex double: answers per prompt template, counts dispatches. `assign` and
 *  `verify` may be functions of the request's own content, so a stubbed reply is
 *  always a real answer to what was asked. */
function stubCodex(opts: {
  assign?: (input: { ids: string[]; prompt: string }) => unknown;
  verify?: (input: { prompt: string }) => unknown;
}) {
  const state = { assign: 0, verify: 0, asked: [] as string[][], models: [] as (string | undefined)[] };
  return {
    state,
    deps: {
      runCodex: async (a: { prompt: string; model?: string }) => {
        const isVerify = a.prompt.includes("=== PROMPT: p4_nl_links_verify ===");
        state.models.push(a.model);
        const ids = objIdsInPrompt(a.prompt);
        let reply: unknown;
        if (isVerify) {
          state.verify++;
          reply = opts.verify?.({ prompt: a.prompt }) ?? { verdicts: verdictsFromPrompt(a.prompt) };
        } else {
          state.assign++;
          state.asked.push(ids);
          reply = opts.assign?.({ ids, prompt: a.prompt }) ?? { blocks: allUnstatedFromPrompt(a.prompt) };
        }
        return { stdout: typeof reply === "string" ? reply : JSON.stringify(reply), stderr: "" };
      },
    },
  };
}

/** Read the rows/displays a request listed and answer every one negatively. */
function allUnstatedFromPrompt(prompt: string): Record<string, unknown> {
  const out: Record<string, { assignments: unknown[]; displayLinks: unknown[] }> = {};
  let obj = "";
  let section = "";
  for (const line of prompt.split("\n")) {
    const head = /^### (.+)$/.exec(line);
    if (head) {
      obj = head[1];
      out[obj] = { assignments: [], displayLinks: [] };
      continue;
    }
    if (/^(LEAN ROWS|PAPER SEGMENTS|DECLARATIONS):$/.test(line)) {
      section = line.slice(0, -1);
      continue;
    }
    if (!obj) continue;
    if (section === "LEAN ROWS") {
      const m = /^(r\d+) \[/.exec(line);
      if (m) out[obj].assignments.push({ row: m[1], unstated: true });
    } else if (section === "PAPER SEGMENTS") {
      const m = /^(s\d+) \[display\]/.exec(line);
      if (m) out[obj].displayLinks.push({ segment: m[1], presentationOnly: true });
    }
  }
  return out;
}

/** Accept every claim a verify request listed. */
function verdictsFromPrompt(prompt: string): Array<{ obj_id: string; claim: string; ok: boolean }> {
  const out: Array<{ obj_id: string; claim: string; ok: boolean }> = [];
  let obj = "";
  let inClaims = false;
  for (const line of prompt.split("\n")) {
    const head = /^### (.+)$/.exec(line);
    if (head) {
      obj = head[1];
      inClaims = false;
      continue;
    }
    if (line === "CLAIMS TO AUDIT:") {
      inClaims = true;
      continue;
    }
    if (/^[A-Z ]+:$/.test(line)) {
      inClaims = false;
      continue;
    }
    const m = inClaims ? /^([rs]\d+) /.exec(line) : null;
    if (m) out.push({ obj_id: obj, claim: m[1], ok: true });
  }
  return out;
}

// ---------------------------------------------------------------------------

describe("segmentation (both invariants hold by construction)", () => {
  it("tiles the block exactly: every byte in exactly one segment, in order", () => {
    const segs = segmentBlock(BLOCK_HTML);
    expect(segmentationProblems(BLOCK_HTML, segs)).toEqual([]);
    expect(segs.map((s) => segmentText(BLOCK_HTML, s)).join("")).toBe(BLOCK_HTML);
  });

  it("takes a display whole and marks it, including one with nested spans", () => {
    const html = `<p>lead in ${DISPLAY(`<span class="frac">a</span> + b`)} tail.</p>`;
    expect(displayRanges(html)).toHaveLength(1);
    const segs = segmentBlock(html);
    const displays = segs.filter((s) => s.kind === "display");
    expect(displays).toHaveLength(1);
    expect(segmentText(html, displays[0])).toBe(DISPLAY(`<span class="frac">a</span> + b`));
    expect(segmentationProblems(html, segs)).toEqual([]);
  });

  it("records the real open-element path, and never closes what it did not open", () => {
    // pandoc nests everything in <p>, so segments legitimately begin inside an
    // open element; what must hold is that each one says so and stays well-nested.
    const html = "<p>Hello. World.</p><ul><li>One. Two.</li></ul>";
    const segs = segmentBlock(html);
    expect(segmentationProblems(html, segs)).toEqual([]);
    expect(segs.length).toBeGreaterThan(2); // sentences inside <p>/<li> still split
    const inParagraph = segs.find((x) => segmentText(html, x).startsWith(" World."));
    expect(inParagraph?.openPath).toEqual(["p"]);
    const inItem = segs.find((x) => segmentText(html, x).includes("Two."));
    expect(inItem?.openPath).toEqual(["ul", "li"]);
    expect(segs[0].openPath).toEqual([]); // the first segment starts at top level
  });

  it("flags a hand-made segment that misreports its path or over-closes", () => {
    const html = "<p>Hello. World.</p>";
    const segs = segmentBlock(html);
    const lying = segs.map((x, i) => (i === 1 ? { ...x, openPath: [] } : x));
    expect(segmentationProblems(html, lying).join("; ")).toMatch(/records openPath \[\], actual \[p\]/);
    // a stray close tag: the path at offset 0 really is empty, so this is caught
    // by the never-close-what-you-did-not-open clause, not by the path check
    const stray = "A.</p>";
    const straySegs = [{ id: "s1", kind: "text" as const, start: 0, end: stray.length, openPath: [] }];
    expect(segmentationProblems(stray, straySegs).join("; ")).toMatch(/closes <\/p> it never had open/);
  });

  it("keeps nested paragraphs, lists and spans well-nested across every segment", () => {
    const html =
      "<p>Alpha. Beta.</p>" +
      `<p>Gamma ${INLINE("\\(x\\)")} delta. ${DISPLAY("\\[y\\]")} Epsilon.</p>` +
      "<ul><li>Item one. Item two.</li><li>Item three.</li></ul>";
    const segs = segmentBlock(html);
    expect(segmentationProblems(html, segs)).toEqual([]);
    expect(segs.map((x) => segmentText(html, x)).join("")).toBe(html);
    // the display inside the paragraph is still its own segment
    const display = segs.find((x) => x.kind === "display");
    expect(display).toBeTruthy();
    expect(display!.openPath).toEqual(["p"]);
  });

  it("never cuts inside a tag or inside inline math", () => {
    const segs = segmentBlock(BLOCK_HTML);
    for (const s of segs) {
      for (const at of [s.start, s.end]) {
        if (at === 0 || at === BLOCK_HTML.length) continue;
        const before = BLOCK_HTML.slice(0, at);
        // not inside a tag: every `<` before the cut is closed before it
        expect(before.lastIndexOf("<")).toBeLessThanOrEqual(before.lastIndexOf(">"));
        // not inside an inline-math element
        const openAt = before.lastIndexOf('<span class="math inline">');
        if (openAt >= 0) expect(before.indexOf("</span>", openAt)).toBeGreaterThanOrEqual(0);
      }
    }
    // the inline formula sentence is one segment, not split at its `\(`
    expect(segs.some((s) => segmentText(BLOCK_HTML, s).includes(INLINE("\\(m>0\\)")))).toBe(true);
  });

  it("splits text runs at sentence ends, and gives stable ids for identical input", () => {
    const segs = segmentBlock(BLOCK_HTML);
    const texts = segs.filter((s) => s.kind === "text").map((s) => segmentText(BLOCK_HTML, s));
    expect(texts.length).toBeGreaterThan(1);
    expect(texts.some((t) => t.includes("The propensity lies in the interval."))).toBe(true);
    expect(segmentBlock(BLOCK_HTML)).toEqual(segs); // deterministic
    expect(segs.map((s) => s.id)).toEqual(segs.map((_, i) => `s${i + 1}`));
  });

  it("handles a block with no display and a block that is one display", () => {
    const plain = "<p>One sentence only.</p>";
    expect(segmentBlock(plain).every((s) => s.kind === "text")).toBe(true);
    expect(segmentationProblems(plain, segmentBlock(plain))).toEqual([]);
    const only = DISPLAY("\\[x\\]");
    expect(segmentBlock(only)).toEqual([
      { id: "s1", kind: "display", start: 0, end: only.length, openPath: [] },
    ]);
  });
});

describe("Lean rows (ported structurer)", () => {
  it("gives every hypothesis and conclusion a stable id in reading order", () => {
    const view = structureStatementView(THEOREM);
    expect(view).not.toBeNull();
    const rows = assignRowIds(view!);
    expect(rows.map((r) => r.id)).toEqual(rows.map((_, i) => `r${i + 1}`));
    expect(rows.filter((r) => r.kind === "hyp").length).toBeGreaterThan(0);
    expect(rows.some((r) => r.kind === "conclusion")).toBe(true);
    // ids land on the tree the site renders, not only on the flat list
    expect(view!.sharedHyps.every((h) => typeof h.id === "string")).toBe(true);
    expect(view!.conclusions.every((c) => typeof c.id === "string")).toBe(true);
  });

  it("gives no id to a purely branching card, so no empty row is invented", () => {
    // a conjunction that splits with no ∃ prefix: the parent card carries `sub`
    // only, and has no content row for the renderer to draw.
    const thm = [
      "theorem both",
      "    (h : True) :",
      "    (1 = 1 ∧ 2 = 2) ∧ 3 = 3",
    ].join("\n");
    const view = structureStatementView(thm);
    expect(view).not.toBeNull();
    const rows = assignRowIds(view!);
    expect(rows.every((r) => r.code.trim().length > 0)).toBe(true);
    const branching = (card: { intro?: string; code?: string; sub?: unknown[]; id?: string }): number =>
      (card.sub && card.intro === undefined && card.code === undefined ? 1 : 0) +
      ((card.sub ?? []) as typeof card[]).reduce((n, c) => n + branching(c), 0);
    const branchingCards = view!.conclusions.reduce((n, c) => n + branching(c), 0);
    if (branchingCards > 0) {
      // every branching card stayed id-less, so it produced no row
      const idsOnBranching = (card: { intro?: string; code?: string; sub?: unknown[]; id?: string }): number =>
        (card.sub && card.intro === undefined && card.code === undefined && card.id !== undefined ? 1 : 0) +
        ((card.sub ?? []) as typeof card[]).reduce((n, c) => n + idsOnBranching(c), 0);
      expect(view!.conclusions.reduce((n, c) => n + idsOnBranching(c), 0)).toBe(0);
    }
    // ids remain a dense reading-order sequence over the rows that DO exist
    expect(rows.map((r) => r.id)).toEqual(rows.map((_, i) => `r${i + 1}`));
  });

  it("lifts conclusion-local lets and exposes the conjunction beneath them", () => {
    const thm = `theorem sharp_sign (x : ℝ) :
      let W := x + 1
      let denominator := W ^ 2 + 1
      let derivative := W / denominator
      HasDerivAt (fun y => y) derivative x ∧
      0 < denominator ∧
      (derivative < 0 ↔ W < 0) := by
    sorry`;
    const view = structureStatementView(thm)!;
    expect(view).not.toBeNull();
    expect(view.conclusions).toHaveLength(1);
    expect(view.conclusions[0].hyps.map((h) => h.code)).toEqual([
      "let W := x + 1",
      "let denominator := W ^ 2 + 1",
      "let derivative := W / denominator",
    ]);
    expect(view.conclusions[0].sub?.map((c) => c.code)).toEqual([
      "HasDerivAt (fun y => y) derivative x",
      "0 < denominator",
      "derivative < 0 ↔ W < 0",
    ]);
    expect(assignRowIds(view).map((r) => r.code)).toEqual([
      "(x : ℝ)",
      "let W := x + 1",
      "let denominator := W ^ 2 + 1",
      "let derivative := W / denominator",
      "HasDerivAt (fun y => y) derivative x",
      "0 < denominator",
      "derivative < 0 ↔ W < 0",
    ]);
  });

  it("peels semicolon lets before splitting their scoped conjunction", () => {
    const view = structureStatementView(`theorem recovery (x : ℝ) :
      (let f := x + 1;
       let Q := f ^ 2;
       Q ≠ 0 ∧ P Q ∧ R Q) := by sorry`)!;
    expect(view.conclusions).toHaveLength(1);
    expect(view.conclusions[0].hyps.map((h) => h.code)).toEqual([
      "let f := x + 1",
      "let Q := f ^ 2",
    ]);
    expect(view.conclusions[0].sub?.map((c) => c.code)).toEqual(["Q ≠ 0", "P Q", "R Q"]);
  });

  it("keeps splitting when lets and governed telescopes alternate", () => {
    const view = structureStatementView(`theorem layered :
      ∃ c : ℝ, 0 < c ∧
      let B := c + 1
      ∀ L : ℝ, B ≤ L →
        let C := L + 1
        0 < C ∧ P C ∧ Q C := by sorry`)!;
    const scoped = view.conclusions[0].sub?.[1];
    expect(scoped?.hyps.map((h) => h.code)).toEqual([
      "let B := c + 1",
      "∀ L : ℝ",
      "B ≤ L",
      "let C := L + 1",
    ]);
    expect(scoped?.sub?.map((c) => c.code)).toEqual(["0 < C", "P C", "Q C"]);
  });

  it("keeps splitting below the former three-level Snipe cutoff", () => {
    const thm = `theorem frontier :
      ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 0 < n →
        Main n ∧
        (∀ M : Model, ∀ r : ℕ, 1 ≤ r → Identity M r ∧ Bound M r ∧ Sharp M r) := by
    sorry`;
    const view = structureStatementView(thm)!;
    const quantified = view.conclusions[0].sub?.[1].sub?.[1];
    expect(quantified?.hyps.map((h) => h.code)).toEqual(["∀ M : Model", "∀ r : ℕ", "1 ≤ r"]);
    expect(quantified?.sub?.map((c) => c.code)).toEqual(["Identity M r", "Bound M r", "Sharp M r"]);
  });

  it("does not mistake a big-operator binder comma for connective scope", () => {
    const view = structureStatementView(`theorem overlap :
      ∀ M : Model, ∀ r : ℕ, 1 ≤ r →
        (∑ i, overlap M i r) = total M r ∧
        total M r ≤ bound M r ∧
        bound M r ≤ sharp M r := by sorry`)!;
    expect(view.sharedHyps.map((h) => h.code)).toEqual(["∀ M : Model", "∀ r : ℕ", "1 ≤ r"]);
    expect(view.conclusions.map((c) => c.code)).toEqual([
      "(∑ i, overlap M i r) = total M r",
      "total M r ≤ bound M r",
      "bound M r ≤ sharp M r",
    ]);
  });

  it("ships a block without rows when the statement is not theorem-like", () => {
    const input = inputFor({ snippet: { ...SNIPPET, statement: "def notATheorem := 1" } });
    expect(input.structured).toBeNull();
    expect(input.rows).toEqual([]);
    expect(input.segments.length).toBeGreaterThan(0); // segments still ship
  });
});

describe("block inputs and cache keys", () => {
  it("binds the artifact to the EXACT bytes the offsets index", () => {
    const input = inputFor();
    expect(input.digest).toBe(rawDigest(BLOCK_HTML));
    expect(input.digest).toMatch(/^[0-9a-f]{64}$/); // raw sha256, not a folded hash
    expect(input.byteLength).toBe(BLOCK_HTML.length);
    // appended whitespace: caught
    const appended = inputFor({ html: `${BLOCK_HTML} ` });
    expect(appended.digest).not.toBe(input.digest);
    expect(appended.key).not.toBe(input.key);
    // whitespace REDISTRIBUTION — the same run of spaces moved from one gap to
    // another. Same length, same folded text, but every offset after the move
    // has shifted. A folded hash and the byte count are both blind to it.
    const base = "<p>alpha  beta gamma. delta.</p>";
    const moved = "<p>alpha beta  gamma. delta.</p>";
    expect(moved.length).toBe(base.length);
    expect(hashEnvBody(moved)).toBe(hashEnvBody(base)); // folded hash: blind
    const a = inputFor({ html: base });
    const b = inputFor({ html: moved });
    expect(b.byteLength).toBe(a.byteLength); // length: blind
    expect(b.digest).not.toBe(a.digest); // raw digest: decisive
    expect(b.key).not.toBe(a.key); // and the cache re-asks
  });

  it("fails the stage when a theorem-kind statement will not structure", () => {
    // a `theorem` the structurer declines is a parser regression, not a rowless
    // object: silently downgrading it would ship a theorem with no rows.
    expect(() => buildBlockInput({
      objId: "t1", blockHtml: BLOCK_HTML, index: index(),
      snippet: { ...SNIPPET, statement: "theorem broken (( : := by trivial" },
    })).toThrow(/parser regression, not a rowless object/);
    // and the kind test reads past docstrings and attributes
    expect(isTheoremLike("/-- doc -/\n@[simp]\ntheorem t : True := trivial")).toBe(true);
    expect(isTheoremLike("noncomputable def d := 1")).toBe(false);
    expect(isTheoremLike("structure S where x : Nat")).toBe(false);
    expect(isTheoremLike("lemma l : True := trivial")).toBe(true);
  });

  it("gives explicit Prop-valued definitions fine-grained rows", () => {
    const statement = `def VCLocalizedEnvelope (P : Law) (α : ℝ) : Prop :=
      ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
        ∀ m : ℕ, 0 < m → EnvelopeBound P α C p m`;
    expect(isPropDefinition(statement)).toBe(true);
    expect(isPropDefinition("def numericEnvelope (α : ℝ) : ℝ := α + 1")).toBe(false);

    const input = inputFor({ snippet: { ...SNIPPET, statement } });
    expect(input.rowless).toBe(false);
    expect(input.structured?.sharedHyps.map((h) => h.code)).toEqual(["(P : Law)", "(α : ℝ)"]);
    expect(input.rows.map((r) => r.code)).toEqual([
      "(P : Law)",
      "(α : ℝ)",
      "∃ C p : ℝ,",
      "0 < C",
      "0 ≤ p",
      "∀ m : ℕ",
      "0 < m",
      "EnvelopeBound P α C p m",
    ]);
  });

  it("structures the unique Prop declaration inside a composite assumption", () => {
    const prop = `def IidSampling {d n : ℕ} (P : Law d) (mu_n : Measure (Fin n → Obs d)) : Prop :=
      mu_n = productLaw P n`;
    const composite: LeanSnippet = {
      ...SNIPPET,
      decl: "(composite)",
      statement: "",
      components: [
        { label: "Ns.IidSampling", statement: prop },
        { label: "Ns.Law", statement: "structure Law (d : ℕ) where pmf : PMF (Obs d)" },
        { label: "Ns.Obs", statement: "abbrev Obs (d : ℕ) := Fin d × Bool × Bool" },
      ],
    };
    const input = inputFor({ snippet: composite });
    expect(input.rowless).toBe(false);
    expect(input.structured?.sharedHyps.map((h) => h.code)).toEqual([
      "{d n : ℕ}",
      "(P : Law d)",
      "(mu_n : Measure (Fin n → Obs d))",
    ]);
    expect(input.structured?.conclusions.map((c) => c.code)).toEqual(["mu_n = productLaw P n"]);

    const ambiguous = inputFor({
      snippet: {
        ...composite,
        components: [
          { label: "Ns.Law", statement: "structure Law (d : ℕ) where pmf : PMF (Obs d)" },
          { label: "Ns.IidSampling", statement: prop },
          { label: "Ns.Overlap", statement: "def Overlap (P : Law d) : Prop := Good P" },
        ],
      },
    });
    expect(ambiguous.rowless).toBe(true);
    expect(ambiguous.structured).toBeNull();
  });

  it("structures a principal Prop-valued record inside a composite definition", () => {
    const experimentClass = `structure ExperimentClass (n : ℕ) {d : ℕ} (epsilon : ℝ)
      (P : Law d) (mu_n : Measure (Fin n → Obs d)) : Prop where
      epsilon_pos : 0 < epsilon
      epsilon_le_half : epsilon ≤ 1 / 2
      product_law : IidSampling P mu_n
      overlap : Overlap epsilon P`;
    const input = inputFor({
      snippet: {
        ...SNIPPET,
        decl: "(composite)",
        statement: "",
        components: [
          { label: "Ns.ExperimentClass", statement: experimentClass },
          { label: "Ns.IidSampling", statement: "def IidSampling (P : Law d) : Prop := Good P" },
          { label: "Ns.Overlap", statement: "def Overlap (P : Law d) : Prop := Good P" },
        ],
      },
    });
    expect(input.rowless).toBe(false);
    expect(input.structured?.sharedHyps.map((h) => h.code)).toEqual([
      "(n : ℕ)",
      "{d : ℕ}",
      "(epsilon : ℝ)",
      "(P : Law d)",
      "(mu_n : Measure (Fin n → Obs d))",
    ]);
    expect(input.structured?.conclusions.map((c) => c.code)).toEqual([
      "epsilon_pos : 0 < epsilon",
      "epsilon_le_half : epsilon ≤ 1 / 2",
      "product_law : IidSampling P mu_n",
      "overlap : Overlap epsilon P",
    ]);
  });

  it("assembles rows, segments, and the declaration vocabulary", () => {
    const input = inputFor();
    expect(input.rows.length).toBeGreaterThan(0);
    expect(input.segments.length).toBeGreaterThan(0);
    expect(input.vocabulary).toContain(SNIPPET.decl);
  });

  it("keys on content, not on packaging", () => {
    const a = inputFor();
    const b = inputFor();
    expect(a.key).toBe(b.key);
    expect(inputFor({ html: `${BLOCK_HTML}<p>More.</p>` }).key).not.toBe(a.key);
    expect(inputFor({ snippet: { ...SNIPPET, statement: `${THEOREM} ∧ True` } }).key).not.toBe(a.key);
  });

  it("caps a verify request by CLAIM COUNT as well as bytes", () => {
    const block = inputFor();
    const claims = block.rows.length + block.segments.filter((x) => x.kind === "display").length;
    expect(claims).toBeGreaterThan(0);
    const v = (objId: string) => ({
      objId, block,
      assignments: block.rows.map((r) => ({ row: r.id, unstated: true as const })),
      displayLinks: block.segments.filter((x) => x.kind === "display")
        .map((x) => ({ segment: x.id, presentationOnly: true as const })),
    });
    expect(claimCount(v("a1"))).toBe(claims);
    const many = ["a", "b", "c", "d", "e", "f"].map(v);
    // bytes alone would batch them all; the claim cap splits them
    const byBytes = chunkBySize(many, verifySection, 10_000_000);
    expect(byBytes).toHaveLength(1);
    const capped = chunkBySize(many, verifySection, 10_000_000, { of: claimCount, max: 2 * claims });
    expect(capped).toHaveLength(3);
    expect(capped.every((c) => c.reduce((n, x) => n + claimCount(x), 0) <= 2 * claims)).toBe(true);
    // a single block over the cap still runs alone rather than being dropped
    const alone = chunkBySize(many, verifySection, 10_000_000, { of: claimCount, max: 1 });
    expect(alone).toHaveLength(6);
    expect(MAX_VERIFY_CLAIMS).toBeLessThanOrEqual(64); // below the largest request that came back whole
  });

  it("packs chunks deterministically, oversized items alone", () => {
    const items = ["c", "a", "b"].map((objId) => ({ objId }));
    expect(chunkBySize(items, (i) => i.objId, 100).map((c) => c.map((i) => i.objId))).toEqual([["a", "b", "c"]]);
    expect(chunkBySize(items, (i) => i.objId, 1).map((c) => c.map((i) => i.objId))).toEqual([["a"], ["b"], ["c"]]);
  });
});

describe("assignment totality (the closed-world contract)", () => {
  const input = () => inputFor();

  it("accepts a total answer", () => {
    const i = input();
    expect(assignmentProblems(i, totalAnswer(i))).toEqual([]);
    // and a positive one
    const positive = {
      assignments: i.rows.map((r, n) => (n === 0 ? { row: r.id, segments: [i.segments[0].id] } : { row: r.id, unstated: true as const })),
      displayLinks: i.segments.filter((s) => s.kind === "display").map((s) => ({ segment: s.id, decl: "Other.unrelated" })),
    };
    expect(assignmentProblems(i, positive)).toEqual([]);
  });

  it("flags an unanswered row and an unanswered display", () => {
    const i = input();
    const t = totalAnswer(i);
    expect(assignmentProblems(i, { ...t, assignments: t.assignments.slice(1) })[0]).toMatch(/row\(s\) unanswered/);
    expect(assignmentProblems(i, { ...t, displayLinks: [] })[0]).toMatch(/display\(s\) unanswered/);
  });

  it("flags an invented row, segment, display, or declaration", () => {
    const i = input();
    const t = totalAnswer(i);
    expect(assignmentProblems(i, { ...t, assignments: [...t.assignments, { row: "r999", unstated: true }] })[0])
      .toMatch(/names row r999, which is not a row/);
    expect(assignmentProblems(i, {
      ...t,
      assignments: t.assignments.map((a, n) => (n === 0 ? { row: a.row, segments: ["s999"] } : a)),
    })[0]).toMatch(/names segment s999/);
    expect(assignmentProblems(i, { ...t, displayLinks: [{ segment: "s999", presentationOnly: true }] })
      .join("; ")).toMatch(/not a display segment/);
    expect(assignmentProblems(i, {
      ...t,
      displayLinks: i.segments.filter((s) => s.kind === "display").map((s) => ({ segment: s.id, decl: "NoSuchDecl" })),
    })[0]).toMatch(/no declaration of this paper's\s*Lean development matches/);
  });

  it("flags a row answered twice, and a row that is both stated and unstated", () => {
    const i = input();
    const t = totalAnswer(i);
    expect(assignmentProblems(i, { ...t, assignments: [...t.assignments, t.assignments[0]] }).join("; "))
      .toMatch(/answered more than once/);
    expect(assignmentProblems(i, {
      ...t,
      assignments: t.assignments.map((a, n) =>
        n === 0 ? { row: a.row, segments: [i.segments[0].id], unstated: true as const } : a),
    })[0]).toMatch(/must name segments or be marked unstated/);
    expect(assignmentProblems(i, {
      ...t,
      assignments: t.assignments.map((a, n) => (n === 0 ? { row: a.row } : a)),
    })[0]).toMatch(/must name segments or be marked unstated/);
  });

  it("flags a display that is both linked and presentation-only, or neither", () => {
    const i = input();
    const t = totalAnswer(i);
    const display = i.segments.find((s) => s.kind === "display")!;
    expect(assignmentProblems(i, {
      ...t, displayLinks: [{ segment: display.id, decl: "Other.unrelated", presentationOnly: true }],
    })[0]).toMatch(/neither names a declaration nor is marked presentation-only/);
    expect(assignmentProblems(i, { ...t, displayLinks: [{ segment: display.id }] })[0])
      .toMatch(/neither names a declaration nor is marked presentation-only/);
  });
});

describe("display vocabulary is the whole development, not the block's window", () => {
  // A display often realizes a declaration the 32-piece closure did not reach —
  // the first live v3 run refused two CORRECT names for exactly that reason.
  const wideIndex = () => buildDeclIndex([
    { name: "Ns.overlap_bound", kind: "theorem", file: "B.lean", line: 1, source: THEOREM },
    { name: "Ns.farAway", kind: "def", file: "B.lean", line: 90, source: "def farAway := 1" },
    { name: "A.shared", kind: "def", file: "A.lean", line: 1, source: "def shared := 1" },
    { name: "B.shared", kind: "def", file: "B.lean", line: 1, source: "def shared := 2" },
  ] as IndexedLeanDecl[]);
  const input = () =>
    buildBlockInput({ objId: "a1", blockHtml: BLOCK_HTML, snippet: SNIPPET, index: wideIndex() })!;
  const linkTo = (i: BlockInput, decl: string) => ({
    assignments: i.rows.map((r) => ({ row: r.id, unstated: true as const })),
    displayLinks: i.segments.filter((s) => s.kind === "display").map((s) => ({ segment: s.id, decl })),
  });

  it("accepts a declaration that is in the index but not among the block's pieces", () => {
    const i = input();
    expect(i.vocabulary).not.toContain("Ns.farAway"); // outside the closure window
    expect(assignmentProblems(i, linkTo(i, "Ns.farAway"))).toEqual([]);
    expect(assignmentProblems(i, linkTo(i, "farAway"))).toEqual([]); // unambiguous short name
    expect(declIsKnown(i.index, "Ns.farAway")).toBe(true);
  });

  it("refuses a declaration the development does not have", () => {
    const i = input();
    expect(assignmentProblems(i, linkTo(i, "NotADecl"))[0])
      .toMatch(/no declaration of this paper's\s*Lean development matches/);
    expect(declIsKnown(i.index, "NotADecl")).toBe(false);
  });

  it("normalizes an accepted decl to its fully-qualified name", () => {
    const i = input();
    expect(resolveDeclName(i.index, "farAway")).toBe("Ns.farAway");       // bare short name
    expect(resolveDeclName(i.index, "Ns.farAway")).toBe("Ns.farAway");    // already qualified
    // the artifact carries the resolved name, never the input string
    const normalized = normalizeDisplayLinks(i.index, [{ segment: "s1", decl: "farAway" }]);
    expect(normalized).toEqual([{ segment: "s1", decl: "Ns.farAway" }]);
    // and presentation-only links pass through untouched
    expect(normalizeDisplayLinks(i.index, [{ segment: "s1", presentationOnly: true }]))
      .toEqual([{ segment: "s1", presentationOnly: true }]);
  });

  it("refuses a qualified name whose prefix contradicts the declaration it would resolve to", () => {
    const i = input();
    // `resolveIndexed`'s short-name fallback would accept this; the producer must
    // not, or it hands the consumer a string its own resolver rejects.
    expect(resolveIndexed(i.index, "Bogus.farAway")?.name).toBe("Ns.farAway"); // the looser helper
    expect(resolveDeclName(i.index, "Bogus.farAway")).toBeNull();              // the strict one
    expect(declIsKnown(i.index, "Bogus.farAway")).toBe(false);
    expect(assignmentProblems(i, linkTo(i, "Bogus.farAway"))[0])
      .toMatch(/prefix contradicts the declaration it would\s*resolve to/);
    // a genuine dotted SUFFIX is fine, and normalizes
    const deep = buildDeclIndex([
      { name: "A.B.C.thing", kind: "def", file: "B.lean", line: 1, source: "def thing := 1" },
    ] as IndexedLeanDecl[]);
    expect(resolveDeclName(deep, "C.thing")).toBe("A.B.C.thing");
    expect(resolveDeclName(deep, "B.C.thing")).toBe("A.B.C.thing");
    expect(resolveDeclName(deep, "X.thing")).toBeNull();
  });

  it("refuses a short name two declarations share, rather than guessing", () => {
    const i = input();
    expect(declIsKnown(i.index, "shared")).toBe(false);
    expect(assignmentProblems(i, linkTo(i, "shared"))[0]).toMatch(/refused rather than guessed/);
    expect(declIsKnown(i.index, "A.shared")).toBe(true); // qualified is fine
  });

  it("accepts several declarations for one display, and refuses a repeat or a mix", () => {
    const i = input();
    const display = i.segments.find((x) => x.kind === "display")!;
    const rows = i.rows.map((r) => ({ row: r.id, unstated: true as const }));
    const links = (entries: Array<{ decl?: string; presentationOnly?: true }>) => ({
      assignments: rows,
      displayLinks: entries.map((e) => ({ segment: display.id, ...e })),
    });
    // one display defining three constants realizes three declarations
    expect(assignmentProblems(i, links([
      { decl: "Ns.farAway" }, { decl: "A.shared" }, { decl: "B.shared" },
    ]))).toEqual([]);
    // the same declaration twice is one link, spelled twice
    expect(assignmentProblems(i, links([{ decl: "Ns.farAway" }, { decl: "farAway" }]))[0])
      .toMatch(/names declaration "Ns.farAway" more than once/);
    // decl + presentationOnly is contradictory, but the decl subsumes it: the
    // reply is coerced, not refused (the validator still rejects it raw, which
    // is what makes the coercion a deliberate step rather than a silent hole).
    const both = links([{ decl: "Ns.farAway" }, { presentationOnly: true } as never]);
    expect(assignmentProblems(i, both)[0]).toMatch(/both linked to a declaration and marked presentation-only/);
    const fixed = coerceDisplayLinks(both.displayLinks);
    expect(fixed.coerced).toEqual([display.id]);
    expect(fixed.links).toEqual([{ segment: display.id, decl: "Ns.farAway" }]);
    expect(assignmentProblems(i, { ...both, displayLinks: fixed.links })).toEqual([]);
    // two presentation-only entries and no decl is NOT coercible: still refused
    const twice = links([{ presentationOnly: true } as never, { presentationOnly: true } as never]);
    expect(coerceDisplayLinks(twice.displayLinks).coerced).toEqual([]);
    expect(assignmentProblems(i, twice)[0]).toMatch(/marked presentation-only more than once/);
    // and a display with no entry at all is still unanswered
    expect(assignmentProblems(i, { assignments: rows, displayLinks: [] })[0])
      .toMatch(/display\(s\) unanswered/);
  });

  it("treats a display's whole declaration set as one claim, replaced as a set", () => {
    const i = input();
    const display = i.segments.find((x) => x.kind === "display")!;
    const v = {
      objId: "a1", block: i,
      assignments: i.rows.map((r) => ({ row: r.id, unstated: true as const })),
      displayLinks: [
        { segment: display.id, decl: "Ns.farAway" },
        { segment: display.id, decl: "A.shared" },
      ],
    };
    // the claim shown to the verifier is the list, and it is ONE claim
    expect(verifySection(v)).toContain(`${display.id} -> Ns.farAway, A.shared`);
    expect(chunkClaims([v]).filter((c) => c.endsWith(display.id))).toHaveLength(1);
    // a correction replaces the set: one entry dropped, one added
    const applied = applyVerdicts(v, [
      { obj_id: "a1", claim: display.id, ok: false, decls: ["A.shared", "B.shared"] },
    ]);
    expect(applied.corrections).toBe(1);
    expect(applied.displayLinks.filter((x) => x.segment === display.id)).toEqual([
      { segment: display.id, decl: "A.shared" },
      { segment: display.id, decl: "B.shared" },
    ]);
    // and it can collapse the whole set to presentation-only
    const collapsed = applyVerdicts(v, [
      { obj_id: "a1", claim: display.id, ok: false, presentationOnly: true as const },
    ]);
    expect(collapsed.displayLinks.filter((x) => x.segment === display.id)).toEqual([
      { segment: display.id, presentationOnly: true },
    ]);
  });

  it("lists every nameable declaration once, and pins the copy-exactly rule", async () => {
    const { presentationPrompt } = await import("../src/presentation/prompt_io.js");
    const i = input();
    const appendix = declVocabularyAppendix(i.index);
    // every name, deduped and sorted, one per line
    expect(appendix.split("\n").slice(2)).toEqual([...new Set(i.index.names)].sort());
    expect(appendix).toContain("Ns.farAway");
    expect(appendix).toMatch(/A name that is not on this list does not exist/);
    // the rule travels in both prompts
    const assign = await presentationPrompt("p4_nl_links", {
      objects_payload: `${assignSection(i)}\n\n${appendix}`,
    });
    expect(assign).toMatch(/Every `decl` must be COPIED from the NAMEABLE DECLARATIONS list/);
    expect(assign).toMatch(/if the quantity's declaration is not on the list under any name, the\s*display is `presentationOnly`, not a guess/);
    // appended ONCE, not per object
    expect(assign.split("NAMEABLE DECLARATIONS").length - 1).toBe(2); // rule mention + the list header
    const verify = await presentationPrompt("p4_nl_links_verify", { claims_payload: appendix });
    expect(verify).toMatch(/COPY any declaration name from the NAMEABLE DECLARATIONS list/);
    expect(verify).toMatch(/never an invented name/);
  });

  it("still refuses a fabricated name, now with the list in front of the model", () => {
    const i = input();
    // the shapes seen live: structure-field-like inventions for real decls that
    // exist under quite different names
    for (const fake of ["RealLaw.propensity", "A1A2Law.muPO", "Ns.farAwayHelper"]) {
      expect(declIsKnown(i.index, fake)).toBe(false);
      expect(assignmentProblems(i, linkTo(i, fake))[0])
        .toMatch(/no declaration of this paper's\s*Lean development matches/);
      expect(declVocabularyAppendix(i.index)).not.toContain(fake);
    }
  });

  it("resolves a cross-package declaration the paper's code references", () => {
    // `paper_library_index.json` lists only the paper's own modules as entries;
    // an upstream declaration its Lean code builds on appears solely in extRefs,
    // and was therefore unnameable — every attempt at it was refused.
    const withExternal = buildDeclIndex([
      { name: "Ns.own", kind: "theorem", file: "B.lean", line: 1, source: "theorem own : True := trivial",
        extRefs: [{ n: "Upstream.Stat.helper", m: "Upstream.Stat.Mod" }] },
      { name: "Ns.collides", kind: "def", file: "B.lean", line: 2, source: "def collides := 1",
        extRefs: [{ n: "Upstream.Other.collides", m: "Upstream.Other" }] },
    ] as IndexedLeanDecl[]);
    expect(resolveDeclName(withExternal, "helper")).toBe("Upstream.Stat.helper");        // bare
    expect(resolveDeclName(withExternal, "Upstream.Stat.helper")).toBe("Upstream.Stat.helper");
    expect(resolveDeclName(withExternal, "Stat.helper")).toBe("Upstream.Stat.helper");   // genuine suffix
    expect(resolveDeclName(withExternal, "Ns.helper")).toBeNull();                       // wrong prefix
    // the paper's OWN declaration keeps a short name it shares with an external
    expect(resolveDeclName(withExternal, "collides")).toBe("Ns.collides");
    // an upstream declaration the paper never references stays unnameable
    expect(resolveDeclName(withExternal, "Upstream.Stat.unreferenced")).toBeNull();
  });

  it("keeps externals out of the closure, which has no source to walk", () => {
    const i = buildBlockInput({
      objId: "a1", blockHtml: BLOCK_HTML, snippet: SNIPPET,
      index: buildDeclIndex([
        { name: "Ns.overlap_bound", kind: "theorem", file: "B.lean", line: 1, source: THEOREM,
          refs: ["Ns.near"], extRefs: [{ n: "Upstream.far", m: "Upstream" }] },
        { name: "Ns.near", kind: "def", file: "B.lean", line: 2, source: "def near := 1" },
      ] as IndexedLeanDecl[]),
    })!;
    expect(i.vocabulary).toContain("Ns.near");            // own def: pulled in
    expect(i.vocabulary).not.toContain("Upstream.far");   // external: nameable, not a piece
    expect(declIsKnown(i.index, "Upstream.far")).toBe(true);
  });

  it("applies the same rule to a verifier correction", () => {
    const i = input();
    const v = {
      objId: "a1", block: i,
      assignments: i.rows.map((r) => ({ row: r.id, unstated: true as const })),
      displayLinks: i.segments.filter((s) => s.kind === "display")
        .map((s) => ({ segment: s.id, presentationOnly: true as const })),
    };
    const all = chunkClaims([v]).map((c) => ({ obj_id: "a1", claim: c.split(" ")[1], ok: true }));
    const disp = v.displayLinks[0].segment;
    expect(verifyProblems([v], all.map((x) => (x.claim === disp ? { ...x, ok: false, decls: ["Ns.farAway"] } : x))))
      .toEqual([]);
    // a correction is normalized to the fully-qualified name too
    const applied = applyVerdicts(v, [{ obj_id: "a1", claim: disp, ok: false, decls: ["farAway"] }]);
    expect(applied.displayLinks.filter((x) => x.segment === disp)).toEqual([{ segment: disp, decl: "Ns.farAway" }]);
    expect(verifyProblems([v], all.map((x) => (x.claim === disp ? { ...x, ok: false, decls: ["Bogus.farAway"] } : x)))[0])
      .toMatch(/no declaration\s*of this paper's Lean development matches/);
    expect(verifyProblems([v], all.map((x) => (x.claim === disp ? { ...x, ok: false, decls: ["shared"] } : x)))[0])
      .toMatch(/no declaration\s*of this paper's Lean development matches/);
  });
});

describe("verification totality and corrections", () => {
  const vi_ = () => {
    const block = inputFor();
    return {
      objId: "a1",
      block,
      assignments: block.rows.map((r) => ({ row: r.id, unstated: true as const })),
      displayLinks: block.segments
        .filter((s) => s.kind === "display")
        .map((s) => ({ segment: s.id, presentationOnly: true as const })),
    };
  };

  it("enumerates every claim, rows and displays alike", () => {
    const v = vi_();
    expect(chunkClaims([v])).toEqual([
      ...v.assignments.map((a) => `a1 ${a.row}`),
      ...v.displayLinks.map((d) => `a1 ${d.segment}`),
    ]);
  });

  it("accepts an exhaustive reply and flags an unjudged, doubled, or invented claim", () => {
    const v = vi_();
    const all = chunkClaims([v]).map((c) => ({ obj_id: "a1", claim: c.split(" ")[1], ok: true }));
    expect(verifyProblems([v], all)).toEqual([]);
    expect(verifyProblems([v], all.slice(1))[0]).toMatch(/claim\(s\) unjudged/);
    expect(verifyProblems([v], [...all, all[0]])[0]).toMatch(/judged more than once/);
    expect(verifyProblems([v], [...all, { obj_id: "a1", claim: "r999", ok: true }])[0])
      .toMatch(/not a claim in this request/);
  });

  it("requires a usable replacement on every rejection", () => {
    const v = vi_();
    const all = chunkClaims([v]).map((c) => ({ obj_id: "a1", claim: c.split(" ")[1], ok: true }));
    const rowClaim = v.assignments[0].row;
    const bad = all.map((x) => (x.claim === rowClaim ? { ...x, ok: false } : x));
    expect(verifyProblems([v], bad)[0]).toMatch(/must name segments or mark it unstated/);
    expect(verifyProblems([v], all.map((x) =>
      x.claim === rowClaim ? { ...x, ok: false, segments: ["s999"] } : x))[0])
      .toMatch(/names unknown segment s999/);
    const dispClaim = v.displayLinks[0].segment;
    expect(verifyProblems([v], all.map((x) =>
      x.claim === dispClaim ? { ...x, ok: false, decls: ["NoSuchDecl"] } : x))[0])
      .toMatch(/no declaration\s*of this paper's Lean development matches/);
    expect(verifyProblems([v], all.map((x) =>
      x.claim === dispClaim ? { ...x, ok: false } : x))[0])
      .toMatch(/must give the declarations it should name/);
  });

  it("flips a wrongly-claimed unstated into the demanded assignment", () => {
    const v = vi_();
    const row = v.assignments[0].row;
    const seg = v.block.segments[0].id;
    const applied = applyVerdicts(v, [{ obj_id: "a1", claim: row, ok: false, segments: [seg] }]);
    expect(applied.corrections).toBe(1);
    expect(applied.assignments.find((a) => a.row === row)).toEqual({ row, segments: [seg] });
    // and the reverse direction: a wrong assignment flipped to unstated
    const v2 = { ...v, assignments: [{ row, segments: [seg] }, ...v.assignments.slice(1)] };
    const back = applyVerdicts(v2, [{ obj_id: "a1", claim: row, ok: false, unstated: true as const }]);
    expect(back.assignments.find((a) => a.row === row)).toEqual({ row, unstated: true });
    // a display correction lands the same way
    const disp = v.displayLinks[0].segment;
    const d = applyVerdicts(v, [{ obj_id: "a1", claim: disp, ok: false, decls: [v.block.vocabulary[0]] }]);
    // the correction is stored fully qualified, not as the short name given
    expect(d.displayLinks.filter((x) => x.segment === disp)).toEqual([
      { segment: disp, decl: resolveDeclName(v.block.index, v.block.vocabulary[0]) },
    ]);
  });

  it("leaves accepted claims untouched", () => {
    const v = vi_();
    const applied = applyVerdicts(v, chunkClaims([v]).map((c) => ({ obj_id: "a1", claim: c.split(" ")[1], ok: true })));
    expect(applied.corrections).toBe(0);
    expect(applied.assignments).toEqual(v.assignments);
    expect(applied.displayLinks).toEqual(v.displayLinks);
  });
});

describe("ensureNlLinks", () => {
  const withDir = async (fn: (dir: string) => Promise<void>) => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "nl-v3-"));
    try {
      await writeIndex(dir, UNRELATED_INDEX);
      await fn(dir);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  };

  type Deps = { runCodex: (a: { prompt: string; model?: string }) => Promise<{ stdout: string; stderr: string }> };
  const run = (dir: string, deps: Deps, entries?: NlLinkSelectable[]) =>
    ensureNlLinks({
      outDir: dir, repoRoot: dir, commit: "deadbeef", qid: "stat_demo", spec: "demo_spec",
      entries: entries ?? [entry("a1")], snippets: { a1: SNIPPET }, paperBodyHtml: PAPER_BODY, deps,
    });

  it("emits the v3 artifact and replays a rerun for free", async () => {
    await withDir(async (dir) => {
      const codex = stubCodex({});
      const first = await run(dir, codex.deps);
      expect(codex.state).toMatchObject({ assign: 1, verify: 1 });
      const artifact = JSON.parse(await readFile(path.join(dir, "nl_links.json"), "utf8"));
      expect(artifact).toMatchObject({
        commit: "deadbeef", qid: "stat_demo", spec: "demo_spec", policy: NL_LINKS_POLICY,
      });
      const block = artifact.blocks.a1;
      expect(block.digest).toBe(rawDigest(extractBlockHtml(PAPER_BODY, "a1")!));
      expect(block.byteLength).toBe(extractBlockHtml(PAPER_BODY, "a1")!.length);
      expect(block.segments.every((x: { openPath?: string[] }) => Array.isArray(x.openPath))).toBe(true);
      expect(block.structured).toBeTruthy();
      expect(block.segments.map((s: { id: string }) => s.id)).toEqual(
        first.artifact.blocks.a1.segments.map((s) => s.id),
      );
      expect(block.assignments).toHaveLength(first.artifact.blocks.a1.segments.length > 0 ? block.assignments.length : 0);
      expect(block.assignments.every((a: { unstated?: boolean }) => a.unstated)).toBe(true);
      expect(block.displayLinks.every((d: { presentationOnly?: boolean }) => d.presentationOnly)).toBe(true);
      expect(first.summary).toMatch(/1 block\(s\), \d+ Lean row\(s\) over \d+ paper segment\(s\)/);

      const second = await run(dir, codex.deps);
      expect(codex.state).toMatchObject({ assign: 1, verify: 1 }); // both caches hit
      expect(second.artifact).toEqual(first.artifact);
    });
  });

  it("re-asks when a cached receipt no longer satisfies totality", async () => {
    await withDir(async (dir) => {
      const codex = stubCodex({});
      await run(dir, codex.deps);
      expect(codex.state.assign).toBe(1);
      // A receipt with the right key but a missing row — as a pre-validator
      // receipt or a hand edit would be. The key alone must not buy trust.
      const cachePath = path.join(dir, "nl_links_cache.json");
      const cache = JSON.parse(await readFile(cachePath, "utf8"));
      cache.a1.assignments = cache.a1.assignments.slice(1);
      await writeFile(cachePath, JSON.stringify(cache), "utf8");
      const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
      try {
        const res = await run(dir, codex.deps);
        expect(codex.state.assign).toBe(2); // re-asked, not replayed
        expect(warn.mock.calls.flat().join(" ")).toMatch(/no longer satisfies the totality contract/);
        expect(res.artifact.blocks.a1.assignments).toHaveLength(
          JSON.parse(await readFile(cachePath, "utf8")).a1.assignments.length,
        );
      } finally {
        warn.mockRestore();
      }
    });
  });

  it("audits every row and display even if the answer under review omits one", async () => {
    await withDir(async (dir) => {
      const input = inputFor();
      const v = {
        objId: "a1", block: input,
        assignments: input.rows.slice(1).map((r) => ({ row: r.id, unstated: true as const })),
        displayLinks: [],
      };
      // The claim set comes from the BLOCK, so the omitted row and the unlinked
      // display are still demanded of the verifier.
      const claims = chunkClaims([v]);
      expect(claims).toContain(`a1 ${input.rows[0].id}`);
      for (const d of input.segments.filter((x) => x.kind === "display")) {
        expect(claims).toContain(`a1 ${d.id}`);
      }
      expect(verifySection(v)).toContain("(NO CLAIM RECORDED)");
    });
  });

  it("re-assigns when the block or the Lean changes, and only then", async () => {
    await withDir(async (dir) => {
      const codex = stubCodex({});
      await run(dir, codex.deps);
      expect(codex.state.assign).toBe(1);
      await ensureNlLinks({
        outDir: dir, repoRoot: dir, commit: "c", qid: "q", spec: "s", entries: [entry("a1")],
        snippets: { a1: { ...SNIPPET, statement: `${THEOREM}\n    ∧ True` } },
        paperBodyHtml: PAPER_BODY, deps: codex.deps,
      });
      expect(codex.state.assign).toBe(2);
    });
  });

  it("asks one request about several blocks, packed in obj_id order", async () => {
    await withDir(async (dir) => {
      const html = ["a1", "b1", "c1"].map((id) =>
        `<div class="formal-block" id="obj-${id}" data-objid="${id}">${BLOCK_HTML}</div>`).join("\n");
      const codex = stubCodex({});
      await ensureNlLinks({
        outDir: dir, repoRoot: dir, commit: "c", qid: "q", spec: "s",
        entries: [entry("c1"), entry("a1"), entry("b1")],
        snippets: { a1: SNIPPET, b1: SNIPPET, c1: SNIPPET },
        paperBodyHtml: html, deps: codex.deps,
      });
      expect(codex.state.assign).toBe(1);
      expect(codex.state.asked).toEqual([["a1", "b1", "c1"]]);
    });
  });

  it("coerces a both-forms display answer, logs it, and still audits the surviving claim", async () => {
    await withDir(async (dir) => {
      let verifyPrompt = "";
      const notes: string[] = [];
      const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
      try {
        const codex = stubCodex({
          // every display gets BOTH a decl link and presentation-only
          assign: ({ prompt }) => {
            const blocks = allUnstatedFromPrompt(prompt) as Record<string, { displayLinks: Array<{ segment: string }> }>;
            for (const b of Object.values(blocks)) {
              b.displayLinks = b.displayLinks.flatMap((d) => [{ segment: d.segment, decl: "Other.unrelated" }, d]);
            }
            return { blocks };
          },
        });
        const deps = {
          runCodex: async (a: { prompt: string; model?: string }) => {
            if (a.prompt.includes("p4_nl_links_verify")) verifyPrompt = a.prompt;
            return codex.deps.runCodex(a);
          },
        };
        const res = await ensureNlLinks({
          outDir: dir, repoRoot: dir, commit: "c", qid: "q", spec: "s", entries: [entry("a1")],
          snippets: { a1: SNIPPET }, paperBodyHtml: PAPER_BODY, deps, log: (m) => notes.push(m),
        });
        // accepted, not refused; the declaration link is what survives
        expect(res.coercions).toBe(1);
        const links = res.artifact.blocks.a1.displayLinks;
        expect(links).toEqual([{ segment: links[0].segment, decl: "Other.unrelated" }]);
        expect(res.summary).toContain("1 contradictory display answer(s) coerced");
        // logged once, naming the object and the segment
        const logged = [...notes, ...warn.mock.calls.flat().map(String)].join(" ");
        expect(logged).toMatch(new RegExp(`a1 display ${links[0].segment} was given both`));
        // and the verifier is asked about the surviving claim, not the dropped one
        expect(verifyPrompt).toContain(`${links[0].segment} -> Other.unrelated`);
        expect(verifyPrompt).not.toContain(`${links[0].segment} PRESENTATION-ONLY`);
      } finally {
        warn.mockRestore();
      }
    });
  });

  it("still refuses the totality violations that are not coercible", async () => {
    await withDir(async (dir) => {
      const codex = stubCodex({
        assign: ({ prompt }) => {
          const blocks = allUnstatedFromPrompt(prompt) as Record<string, { displayLinks: unknown[] }>;
          for (const b of Object.values(blocks)) b.displayLinks = [...b.displayLinks, ...b.displayLinks];
          return { blocks }; // presentation-only twice, no decl: not coercible
        },
      });
      await expect(run(dir, codex.deps)).rejects.toThrow(/marked presentation-only more than once/);
      expect(JSON.parse(await readFile(path.join(dir, "nl_links_cache.json"), "utf8"))).toEqual({});
    });
  });

  it("applies a verifier correction to what ships and to the cache", async () => {
    await withDir(async (dir) => {
      const codex = stubCodex({
        verify: ({ prompt }) => {
          const verdicts = verdictsFromPrompt(prompt);
          // flip the first row claim to a demanded assignment on s1
          return {
            verdicts: verdicts.map((v, n) =>
              n === 0 ? { ...v, ok: false, segments: ["s1"] } : v),
          };
        },
      });
      const res = await run(dir, codex.deps);
      expect(res.corrections).toBe(1);
      const first = res.artifact.blocks.a1.assignments![0];
      expect(first).toEqual({ row: "r1", segments: ["s1"] });
      const cache = JSON.parse(await readFile(path.join(dir, "nl_links_cache.json"), "utf8"));
      expect(cache.a1.assignments[0]).toEqual({ row: "r1", segments: ["s1"] });
      // the corrected state is what replays
      const again = await run(dir, codex.deps);
      expect(codex.state.assign).toBe(1);
      expect(again.artifact.blocks.a1.assignments![0]).toEqual({ row: "r1", segments: ["s1"] });
    });
  });

  it.each([
    ["a skipped object", (p: string) => {
      const blocks = allUnstatedFromPrompt(p);
      delete blocks[Object.keys(blocks)[0]];
      return { blocks };
    }],
    ["an invented object", (p: string) => ({ blocks: { ...allUnstatedFromPrompt(p), ghost: { assignments: [], displayLinks: [] } } })],
  ])("throws uncached when the assignment reply has %s", async (_label, assign) => {
    await withDir(async (dir) => {
      const codex = stubCodex({ assign: ({ prompt }) => assign(prompt) });
      await expect(run(dir, codex.deps)).rejects.toThrow(/must answer exactly the objects asked about/);
      expect(JSON.parse(await readFile(path.join(dir, "nl_links_cache.json"), "utf8"))).toEqual({});
    });
  });

  it.each([
    ["an unanswered row", (p: string) => {
      const blocks = allUnstatedFromPrompt(p) as Record<string, { assignments: unknown[] }>;
      for (const b of Object.values(blocks)) b.assignments = b.assignments.slice(1);
      return { blocks };
    }],
    ["an unanswered display", (p: string) => {
      const blocks = allUnstatedFromPrompt(p) as Record<string, { displayLinks: unknown[] }>;
      for (const b of Object.values(blocks)) b.displayLinks = [];
      return { blocks };
    }],
    ["an invented segment", (p: string) => {
      const blocks = allUnstatedFromPrompt(p) as Record<string, { assignments: Array<{ row: string }> }>;
      for (const b of Object.values(blocks)) b.assignments[0] = { row: b.assignments[0].row, segments: ["s999"] } as never;
      return { blocks };
    }],
  ])("throws uncached when the assignment is not total: %s", async (_label, assign) => {
    await withDir(async (dir) => {
      const codex = stubCodex({ assign: ({ prompt }) => assign(prompt) });
      await expect(run(dir, codex.deps)).rejects.toThrow(/is not total/);
      expect(JSON.parse(await readFile(path.join(dir, "nl_links_cache.json"), "utf8"))).toEqual({});
    });
  });

  it("retries a malformed assignment once with deterministic validator feedback", async () => {
    await withDir(async (dir) => {
      let attempt = 0;
      const prompts: string[] = [];
      const codex = stubCodex({ assign: ({ prompt }) => {
        prompts.push(prompt);
        const blocks = allUnstatedFromPrompt(prompt) as Record<string, {
          assignments: unknown[];
          displayLinks: unknown[];
        }>;
        if (attempt++ === 0) {
          const textSegment = prompt.match(/^(s\d+) \[text\]/m)![1];
          blocks.a1.displayLinks = [{ segment: textSegment, presentationOnly: true }];
        }
        return { blocks };
      }});
      await expect(run(dir, codex.deps)).resolves.toBeDefined();
      expect(codex.state.assign).toBe(2);
      expect(prompts[1]).toMatch(/CORRECTION REQUIRED/);
      expect(prompts[1]).toMatch(/displayLinks may name only segments explicitly labeled \[display\]/);
      expect(prompts[1]).toMatch(/not a display segment/);
    });
  });

  it("throws uncached when the verification skips a claim", async () => {
    await withDir(async (dir) => {
      const codex = stubCodex({ verify: ({ prompt }) => ({ verdicts: verdictsFromPrompt(prompt).slice(1) }) });
      await expect(run(dir, codex.deps)).rejects.toThrow(/did not judge every claim exactly once/);
      await expect(readFile(path.join(dir, "nl_links_verify_cache.json"), "utf8")).rejects.toThrow(/ENOENT/);
      // the assignment receipt survives: the failure is downstream of it
      expect(Object.keys(JSON.parse(await readFile(path.join(dir, "nl_links_cache.json"), "utf8")))).toEqual(["a1"]);
    });
  });

  it("throws on unparseable replies from either pass", async () => {
    await withDir(async (dir) => {
      const bad = stubCodex({ assign: () => "no json here" });
      await expect(run(dir, bad.deps)).rejects.toThrow(/returned invalid JSON/);
    });
    await withDir(async (dir) => {
      const bad = stubCodex({ verify: () => "still no json" });
      await expect(run(dir, bad.deps)).rejects.toThrow(/verification returned invalid JSON/);
    });
  });

  it("ships a def-kind block as rowless BY DESIGN, marked as such", async () => {
    await withDir(async (dir) => {
      const notes: string[] = [];
      const codex = stubCodex({});
      const res = await ensureNlLinks({
        outDir: dir, repoRoot: dir, commit: "c", qid: "q", spec: "s", entries: [entry("a1")],
        snippets: { a1: { ...SNIPPET, statement: "def notATheorem := 1" } },
        paperBodyHtml: PAPER_BODY, deps: codex.deps, log: (m) => notes.push(m),
      });
      expect(res.unstructured).toEqual(["a1"]);
      expect(res.artifact.blocks.a1.structured).toBeUndefined();
      expect(res.artifact.blocks.a1.rowless).toBe(true); // intentional, and said so
      expect(res.artifact.blocks.a1.segments.length).toBeGreaterThan(0);
      // both lists are ALWAYS arrays, so a consumer never guards an access
      expect(res.artifact.blocks.a1.assignments).toEqual([]);
      expect(Array.isArray(res.artifact.blocks.a1.displayLinks)).toBe(true);
      // the display still gets linked, so the call is still made
      expect(codex.state.assign).toBe(1);
      expect(notes.join(" ")).toMatch(/rowless by design/);
    });
  });

  it("makes no call for a block with neither rows nor displays", async () => {
    await withDir(async (dir) => {
      const html = '<div class="formal-block" id="obj-a1" data-objid="a1"><p>Just prose.</p></div>';
      const codex = stubCodex({});
      const res = await ensureNlLinks({
        outDir: dir, repoRoot: dir, commit: "c", qid: "q", spec: "s", entries: [entry("a1")],
        snippets: { a1: { ...SNIPPET, statement: "def notATheorem := 1" } },
        paperBodyHtml: html, deps: codex.deps,
      });
      expect(codex.state).toMatchObject({ assign: 0, verify: 0 });
      expect(res.artifact.blocks.a1.segments.length).toBeGreaterThan(0);
      expect(res.artifact.blocks.a1.assignments).toEqual([]);
      expect(res.artifact.blocks.a1.displayLinks).toEqual([]);
    });
  });

  it("skips web-only envs, synthesized blocks, and objects with no snippet", async () => {
    await withDir(async (dir) => {
      const codex = stubCodex({});
      const res = await ensureNlLinks({
        outDir: dir, repoRoot: dir, commit: "c", qid: "q", spec: "s",
        entries: [
          entry("a1", { env: "citedv" }), entry("a1", { env: "auxiliary" }),
          entry("a1", { env: "symbol" }), entry("a1", { status: "presentation-synthesized" }),
          entry("no-snippet"),
        ],
        snippets: { a1: SNIPPET }, paperBodyHtml: PAPER_BODY, deps: codex.deps,
      });
      expect(codex.state.assign).toBe(0);
      expect(res.blocks).toBe(0);
      expect(selectsForNlLinks({ env: "citedv", status: "matched" })).toBe(false);
      expect(selectsForNlLinks({ env: "assumptionv", status: "matched" })).toBe(true);
    });
  });

  it("fails loudly when the declaration index is missing or empty", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "nl-v3-noindex-"));
    try {
      const codex = stubCodex({});
      await expect(run(dir, codex.deps)).rejects.toThrow(/paper_library_index\.json is missing/);
      expect(codex.state.assign).toBe(0);
      await writeIndex(dir, []);
      await expect(run(dir, codex.deps)).rejects.toThrow(/lists no declarations/);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("treats a corrupted cache as empty-with-warning, then repairs it", async () => {
    await withDir(async (dir) => {
      await writeFile(path.join(dir, "nl_links_cache.json"), '{"a1": {"pol', "utf8");
      const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
      try {
        const codex = stubCodex({});
        await run(dir, codex.deps);
        expect(warn.mock.calls.flat().join(" ")).toMatch(/unreadable.*empty cache/s);
        const repaired = JSON.parse(await readFile(path.join(dir, "nl_links_cache.json"), "utf8"));
        expect(repaired.a1).toMatchObject({ policy: NL_LINKS_POLICY, complete: true });
        await run(dir, codex.deps);
        expect(codex.state.assign).toBe(1); // no re-bill loop
      } finally {
        warn.mockRestore();
      }
    });
  });

  it("refuses a request over the prompt ceiling instead of dispatching it", async () => {
    await withDir(async (dir) => {
      const huge = "x".repeat(MAX_PROMPT_BYTES + 1);
      const codex = stubCodex({});
      await expect(ensureNlLinks({
        outDir: dir, repoRoot: dir, commit: "c", qid: "q", spec: "s", entries: [entry("big")],
        snippets: { big: SNIPPET },
        paperBodyHtml: `<div class="formal-block" id="obj-big" data-objid="big"><p>${huge}</p></div>`,
        deps: codex.deps,
      })).rejects.toThrow(/over the \d+-byte prompt ceiling/);
      expect(codex.state.assign).toBe(0);
    });
  });

  it("verifies on the presentation tier", async () => {
    await withDir(async (dir) => {
      const codex = stubCodex({});
      await run(dir, codex.deps);
      const { MODELS } = await import("../src/models.js");
      // assignment uses the default; verification pins the tier explicitly
      expect(codex.state.models).toContain(MODELS.codexPresentation);
    });
  });
});

describe("Lean reference closure (the decl vocabulary for display links)", () => {
  const idx = (over: Partial<IndexedLeanDecl> & { name: string }): IndexedLeanDecl => ({
    kind: "def", file: "Basic.lean", line: 1, source: `def ${over.name.split(".").pop()} := 0`, ...over,
  });
  const built = () => buildDeclIndex([
    idx({ name: "Ns.Overlap", line: 10, source: "def Overlap := cellPhi", refs: ["Ns.cellPhi"] }),
    idx({ name: "Ns.cellPhi", line: 20, source: "def cellPhi := vectorMass", proofRefs: ["Ns.vectorMass"] }),
    idx({ name: "Ns.vectorMass", line: 30, source: "def vectorMass := armMass", refs: ["Ns.armMass"] }),
    idx({ name: "Ns.armMass", line: 40, source: "def armMass := deep", refs: ["Ns.deep"] }),
    idx({ name: "Ns.deep", line: 50, source: "def deep := 0" }),
  ]);

  it("resolves by fully-qualified name and by unambiguous short name", () => {
    const i = buildDeclIndex([idx({ name: "A.dup" }), idx({ name: "B.dup" }), idx({ name: "A.solo" })]);
    expect(resolveIndexed(i, "A.dup")?.name).toBe("A.dup");
    expect(resolveIndexed(i, "solo")?.name).toBe("A.solo");
    expect(resolveIndexed(i, "dup")).toBeNull();
  });

  it("counts proofRefs for a def, whose body is its statement", () => {
    const i = built();
    expect(referencedDecls(i, i.byName.get("Ns.cellPhi")!).map((d) => d.name)).toEqual(["Ns.vectorMass"]);
  });

  it("walks def-kind refs to depth 5 in depth/file/line order", () => {
    expect(closurePieces({ seedNames: ["Overlap"], index: built(), existing: [] }).map((p) => p.label))
      .toEqual(["Ns.cellPhi", "Ns.vectorMass", "Ns.armMass", "Ns.deep"]);
  });

  it("skips oversized helpers and non-def declarations, and dedupes what is shown", () => {
    const i = buildDeclIndex([
      idx({ name: "Ns.seed", source: "def seed := x", refs: ["Ns.folded", "Ns.thm", "Ns.small"] }),
      idx({ name: "Ns.folded", source: `def folded :=\n${"  step\n".repeat(60)}` }),
      idx({ name: "Ns.thm", kind: "theorem", source: "theorem thm : True := trivial" }),
      idx({ name: "Ns.small", source: "def small := 1" }),
    ]);
    expect(closurePieces({ seedNames: ["Ns.seed"], index: i, existing: [] }).map((p) => p.label))
      .toEqual(["Ns.small"]);
    expect(closurePieces({
      seedNames: ["Ns.seed"], index: i,
      existing: [{ part: "small", label: "small", text: "def small := 1" }],
    })).toEqual([]);
  });

  it("truncates a pathological closure deterministically", () => {
    const many = [idx({ name: "Ns.seed", source: "def seed := x", refs: Array.from({ length: 40 }, (_, k) => `Ns.d${k}`) })];
    for (let k = 0; k < 40; k++) many.push(idx({ name: `Ns.d${k}`, line: k + 1, source: `def d${k} := 0` }));
    const pieces = closurePieces({ seedNames: ["Ns.seed"], index: buildDeclIndex(many), existing: [], maxPieces: 5 });
    expect(pieces.map((p) => p.label)).toEqual(["Ns.d0", "Ns.d1", "Ns.d2", "Ns.d3", "Ns.d4"]);
  });

  it("puts the statement first and the closure after it", () => {
    const pieces = leanPiecesWithClosure({ ...SNIPPET, decl: "Overlap" }, built());
    expect(pieces[0].part).toBe(STATEMENT_PART);
    expect(leanPromptText(pieces)).toContain("-- Ns.cellPhi");
    expect(leanPieces(SNIPPET)).toHaveLength(1);
  });
});


describe("replay idempotence (a rerun must cost nothing and change nothing)", () => {
  const withDir = async (fn: (dir: string) => Promise<void>) => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "nl-replay-"));
    try {
      await writeIndex(dir, UNRELATED_INDEX);
      await fn(dir);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  };
  const files = ["nl_links.json", "nl_links_cache.json", "nl_links_verify_cache.json"];
  const snapshot = async (dir: string) =>
    Object.fromEntries(await Promise.all(files.map(async (f) =>
      [f, await readFile(path.join(dir, f), "utf8").catch(() => "<absent>")] as const)));

  const run = (dir: string, deps: { runCodex: (a: { prompt: string; model?: string }) => Promise<{ stdout: string; stderr: string }> }) =>
    ensureNlLinks({
      outDir: dir, repoRoot: dir, commit: "c", qid: "q", spec: "s",
      entries: [entry("a1")], snippets: { a1: SNIPPET }, paperBodyHtml: PAPER_BODY, deps,
    });

  it("costs nothing and changes nothing on a rerun, with an all-ok verifier", async () => {
    await withDir(async (dir) => {
      const codex = stubCodex({});
      await run(dir, codex.deps);
      const after1 = await snapshot(dir);
      const spent = { assign: codex.state.assign, verify: codex.state.verify };
      await run(dir, codex.deps);
      expect({ assign: codex.state.assign, verify: codex.state.verify }).toEqual(spent);
      expect(await snapshot(dir)).toEqual(after1);
    });
  });

  it("costs nothing on a rerun even when the first run was corrected", async () => {
    await withDir(async (dir) => {
      // A correction rewrites the assignment, so the next run asks a DIFFERENT
      // question about that block. The corrected state is what the verifier
      // itself just prescribed, so it is recorded as already-verified rather
      // than re-audited — otherwise every correction costs a call for ever.
      const codex = stubCodex({
        verify: ({ prompt }) => ({
          verdicts: verdictsFromPrompt(prompt).map((v, n) =>
            n === 0 ? { ...v, ok: false, segments: ["s1"] } : v),
        }),
      });
      const first = await run(dir, codex.deps);
      expect(first.corrections).toBe(1);
      const spent = { assign: codex.state.assign, verify: codex.state.verify };
      const after1 = await snapshot(dir);
      const second = await run(dir, codex.deps);
      expect({ assign: codex.state.assign, verify: codex.state.verify }).toEqual(spent); // FREE
      expect(second.corrections).toBe(0); // the correction is already in place
      expect(second.artifact.blocks.a1.assignments).toEqual(first.artifact.blocks.a1.assignments);
      expect(await snapshot(dir)).toEqual(after1);
    });
  });

  it("does not re-bill a block's batch-mates when only that block changed", async () => {
    await withDir(async (dir) => {
      // Three blocks in one request. The verifier corrects a claim in ONE of
      // them. Keying receipts per chunk made the changed block re-key its two
      // innocent neighbours as well — this is that regression.
      const html = ["a1", "b1", "c1"].map((id) =>
        `<div class="formal-block" id="obj-${id}" data-objid="${id}">${BLOCK_HTML}</div>`).join("\n");
      const snippets = { a1: SNIPPET, b1: SNIPPET, c1: SNIPPET };
      const entries = [entry("a1"), entry("b1"), entry("c1")];
      const codex = stubCodex({
        verify: ({ prompt }) => ({
          verdicts: verdictsFromPrompt(prompt).map((v) =>
            v.obj_id === "b1" && v.claim === "r1" ? { ...v, ok: false, segments: ["s1"] } : v),
        }),
      });
      const call = () => ensureNlLinks({
        outDir: dir, repoRoot: dir, commit: "c", qid: "q", spec: "s",
        entries, snippets, paperBodyHtml: html, deps: codex.deps,
      });
      const first = await call();
      expect(first.corrections).toBe(1);
      expect(codex.state.verify).toBe(1); // one batched request for all three
      const after1 = await snapshot(dir);
      await call();
      expect(codex.state.verify).toBe(1); // nothing re-billed: not b1, not its neighbours
      expect(codex.state.assign).toBe(1);
      expect(await snapshot(dir)).toEqual(after1);
    });
  });

  it("leaves every receipt keyed where it was — the appendix moves no key", async () => {
    await withDir(async (dir) => {
      const codex = stubCodex({});
      await run(dir, codex.deps);
      const keysBefore = {
        assign: Object.entries(JSON.parse(await readFile(path.join(dir, "nl_links_cache.json"), "utf8")))
          .map(([k, v]) => `${k}:${(v as { key: string }).key}`).sort(),
        verify: Object.keys(JSON.parse(await readFile(path.join(dir, "nl_links_verify_cache.json"), "utf8"))).sort(),
      };
      // The appendix is a REQUEST-level addition; block keys hash inputs and
      // per-block claim sections, so a rerun must hit every receipt.
      await run(dir, codex.deps);
      expect({
        assign: Object.entries(JSON.parse(await readFile(path.join(dir, "nl_links_cache.json"), "utf8")))
          .map(([k, v]) => `${k}:${(v as { key: string }).key}`).sort(),
        verify: Object.keys(JSON.parse(await readFile(path.join(dir, "nl_links_verify_cache.json"), "utf8"))).sort(),
      }).toEqual(keysBefore);
      expect(codex.state).toMatchObject({ assign: 1, verify: 1 });
    });
  });

  it("keeps the verify receipt it just wrote — pruning must not delete live keys", async () => {
    await withDir(async (dir) => {
      const codex = stubCodex({});
      await run(dir, codex.deps);
      const cache = JSON.parse(await readFile(path.join(dir, "nl_links_verify_cache.json"), "utf8"));
      expect(Object.keys(cache).length).toBeGreaterThan(0);
      await run(dir, codex.deps);
      expect(JSON.parse(await readFile(path.join(dir, "nl_links_verify_cache.json"), "utf8"))).toEqual(cache);
      expect(codex.state.verify).toBe(1);
    });
  });
});


describe("splitting a block that is too big for one verification request", () => {
  const withDir = async (fn: (dir: string) => Promise<void>) => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "nl-split-"));
    try {
      await writeIndex(dir, UNRELATED_INDEX);
      await fn(dir);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  };

  /** A theorem with `n` hypotheses — the live blocker was 71 claims in one block. */
  const bigTheorem = (n: number) =>
    ["theorem big", ...Array.from({ length: n }, (_, k) => `    (h${k} : 0 < ${k + 1})`), "    : True"].join("\n");
  const BIG = { ...SNIPPET, decl: "big", statement: bigTheorem(70) };
  const bigInput = () => inputFor({ snippet: BIG });

  const unitOf = (input: ReturnType<typeof bigInput>) => ({
    objId: "a1", block: input,
    assignments: input.rows.map((r) => ({ row: r.id, unstated: true as const })),
    displayLinks: input.segments.filter((x) => x.kind === "display")
      .map((x) => ({ segment: x.id, presentationOnly: true as const })),
  });

  it("cuts an over-cap block into consecutive claim groups, deterministically", () => {
    const v = unitOf(bigInput());
    const total = claimCount(v);
    expect(total).toBeGreaterThan(MAX_VERIFY_CLAIMS); // reproduces the blocked shape
    const units = verifyUnits(v);
    expect(units.length).toBe(Math.ceil(total / MAX_VERIFY_CLAIMS));
    expect(units.every((u) => u.claims.length <= MAX_VERIFY_CLAIMS)).toBe(true);
    // a partition of the block's claims, in claim order, with nothing lost
    expect(units.flatMap((u) => u.claims)).toEqual(chunkClaims([v]).map((c) => c.slice("a1 ".length)));
    expect(verifyUnits(v)).toEqual(units); // same split every run
  });

  it("repeats the block's full context in each request, but only its own claims", () => {
    const v = unitOf(bigInput());
    const [first, second] = verifyUnits(v);
    const a = verifySectionFor(v, new Set(first.claims));
    const b = verifySectionFor(v, new Set(second.claims));
    for (const section of [a, b]) {
      expect(section).toContain("PAPER SEGMENTS:");
      expect(section).toContain("LEAN ROWS:");
      expect(section).toContain("DECLARATIONS:");
      // every row is listed as context in both halves
      expect(section).toContain(v.block.rows[0].code.replace(/\n\s*/g, " "));
    }
    // but the CLAIMS are disjoint
    const claimsIn = (section: string) =>
      section.slice(section.indexOf("CLAIMS TO AUDIT:")).split("\n").slice(1)
        .flatMap((l) => /^([rs]\d+) /.exec(l)?.[1] ?? []);
    expect(claimsIn(a)).toEqual(first.claims);
    expect(claimsIn(b)).toEqual(second.claims);
    expect(claimsIn(a).filter((c) => claimsIn(b).includes(c))).toEqual([]);
  });

  it("holds each request to its own subset, not the block's whole claim set", () => {
    const v = unitOf(bigInput());
    const [first] = verifyUnits(v);
    const answered = first.claims.map((c) => ({ obj_id: "a1", claim: c, ok: true }));
    expect(verifyUnitProblems([first], answered)).toEqual([]);          // complete for the subset
    expect(verifyProblems([v], answered)[0]).toMatch(/claim\(s\) unjudged/); // incomplete for the block
    // and a verdict on a claim this request did not ask about is still refused
    const outside = verifyUnits(v)[1].claims[0];
    expect(verifyUnitProblems([first], [...answered, { obj_id: "a1", claim: outside, ok: true }])[0])
      .toMatch(/not a claim in this request/);
  });

  it("splits the run into two requests and caches the block only once both land", async () => {
    await withDir(async (dir) => {
      const codex = stubCodex({});
      const res = await ensureNlLinks({
        outDir: dir, repoRoot: dir, commit: "c", qid: "q", spec: "s", entries: [entry("a1")],
        snippets: { a1: BIG }, paperBodyHtml: PAPER_BODY, deps: codex.deps,
      });
      expect(codex.state.verify).toBe(2); // the 70-hypothesis block did not fit in one
      const cache = JSON.parse(await readFile(path.join(dir, "nl_links_verify_cache.json"), "utf8"));
      expect(Object.keys(cache)).toHaveLength(1); // ONE receipt for the whole block
      expect(cache[Object.keys(cache)[0]].verdicts).toHaveLength(res.rows + res.artifact.blocks.a1.displayLinks.length);
      // and a rerun is free
      await ensureNlLinks({
        outDir: dir, repoRoot: dir, commit: "c", qid: "q", spec: "s", entries: [entry("a1")],
        snippets: { a1: BIG }, paperBodyHtml: PAPER_BODY, deps: codex.deps,
      });
      expect(codex.state.verify).toBe(2);
    });
  });

  it("re-asks only the missing request when the first run was interrupted", async () => {
    await withDir(async (dir) => {
      // die after the first request lands
      let n = 0;
      const dying = {
        runCodex: async (a: { prompt: string; model?: string }) => {
          if (a.prompt.includes("p4_nl_links_verify") && ++n === 2) throw new Error("slurm expiry");
          return stubCodex({}).deps.runCodex(a);
        },
      };
      const call = (deps: typeof dying) => ensureNlLinks({
        outDir: dir, repoRoot: dir, commit: "c", qid: "q", spec: "s", entries: [entry("a1")],
        snippets: { a1: BIG }, paperBodyHtml: PAPER_BODY, deps,
      });
      await expect(call(dying)).rejects.toThrow(/slurm expiry/);
      // a half-audited block cached nothing, so nothing false was recorded
      const partial = JSON.parse(
        await readFile(path.join(dir, "nl_links_verify_cache.json"), "utf8").catch(() => "{}"));
      expect(Object.keys(partial)).toHaveLength(0);
      // the resumed run pays for the verification again, but not for assignment
      const codex = stubCodex({});
      await call(codex.deps);
      expect(codex.state.assign).toBe(0); // the assignment receipt survived
      expect(codex.state.verify).toBe(2);
    });
  });

  it("leaves an under-cap block packed and keyed exactly as before", async () => {
    await withDir(async (dir) => {
      const codex = stubCodex({});
      await ensureNlLinks({
        outDir: dir, repoRoot: dir, commit: "c", qid: "q", spec: "s", entries: [entry("a1")],
        snippets: { a1: SNIPPET }, paperBodyHtml: PAPER_BODY, deps: codex.deps,
      });
      expect(codex.state.verify).toBe(1); // one request, as before the split
      const small = unitOf(inputFor());
      expect(verifyUnits(small)).toHaveLength(1);
      // the cache key still hashes the FULL-claim rendering, so no key moved
      expect(verifyCacheKey(small)).toBe(
        (await import("../src/presentation/tex_anchors.js")).hashEnvBody(
          `${NL_LINKS_POLICY}|verify|${verifySection(small)}`),
      );
      const keys = Object.keys(JSON.parse(await readFile(path.join(dir, "nl_links_verify_cache.json"), "utf8")));
      expect(keys).toEqual([verifyCacheKey(small)]);
    });
  });
});

describe("prompts", () => {
  it("states the closed-world assignment contract and renders every placeholder", async () => {
    const { presentationPrompt } = await import("../src/presentation/prompt_io.js");
    const input = inputFor();
    const prompt = await presentationPrompt("p4_nl_links", { objects_payload: assignSection(input) });
    expect(prompt.match(/\{\{[a-z_]+\}\}/g)).toBeNull();
    expect(prompt).toContain("### a1");
    expect(prompt).toContain("LEAN ROWS:");
    expect(prompt).toContain("PAPER SEGMENTS:");
    expect(prompt).toMatch(/You choose only among these ids and names; you never quote, rewrite, or compose text/);
    expect(prompt).toMatch(/The answer must be TOTAL/);
    expect(prompt).toMatch(/every row\s*id appears exactly once/);
    expect(prompt).toMatch(/either with one or more `decl` entries/);
    expect(prompt).toMatch(/never the same declaration twice for one segment/);
    expect(prompt).toMatch(/realizes one declaration per quantity: give an entry for each/);
    // the borderline that stopped a live rollout: notation AND realized is realized
    expect(prompt).toMatch(/Mark a display `presentationOnly` only\s*when NO declaration realizes it/);
    expect(prompt).toMatch(/A display that introduces notation is not presentation-only if some\s*declaration realizes it anyway/);
    expect(prompt).toMatch(/the two\s*forms are never given together for one segment/);
    expect(prompt).toMatch(/Mark a row `unstated` when the block does not state it/);
    expect(prompt).toMatch(/that is the\s*declaration for the whole quantity, not a helper/);
    expect(prompt).toMatch(/any declaration of the development may be named/);
    expect(prompt).not.toContain("GLOBAL READER-FACING PROSE CONTRACT"); // verdict-only
  });

  it("asks the verifier to audit negative claims too, and to correct in place", async () => {
    const { presentationPrompt } = await import("../src/presentation/prompt_io.js");
    const block = inputFor();
    const prompt = await presentationPrompt("p4_nl_links_verify", {
      claims_payload: verifySection({
        objId: "a1", block,
        assignments: block.rows.map((r) => ({ row: r.id, unstated: true as const })),
        displayLinks: block.segments.filter((s) => s.kind === "display")
          .map((s) => ({ segment: s.id, presentationOnly: true as const })),
      }),
    });
    expect(prompt.match(/\{\{[a-z_]+\}\}/g)).toBeNull();
    expect(prompt).toContain("CLAIMS TO AUDIT:");
    expect(prompt).toMatch(/Assume some are wrong/);
    expect(prompt).toMatch(/This is the claim most often\s*wrong, so check it directly/);
    expect(prompt).toMatch(/including when the display also introduces\s*notation, since realizing a declaration settles it either way/);
    expect(prompt).toMatch(/Every claim above must be judged exactly once/);
    expect(prompt).toMatch(/you\s*must give the replacement in the same verdict/);
    expect(prompt).not.toContain("GLOBAL READER-FACING PROSE CONTRACT");
  });
});
