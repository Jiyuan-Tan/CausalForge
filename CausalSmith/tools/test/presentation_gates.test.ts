import { describe, it, expect } from "vitest";
import {
  runHardGates,
  gateLoop,
  medianRubric,
  parseRubricReview,
  parseJsonLoose,
  citingSentences,
  type GateRunners,
  type HardGateInput,
} from "../src/presentation/gates.js";
import { parseAnchoredEnvs, hashEnvBody } from "../src/presentation/tex_anchors.js";
import { parseBib } from "../src/presentation/citations.js";

const PAPER = `
\\begin{abstract}We prove a bound \\citep{robins1994}.\\end{abstract}
\\section{Introduction}Intro.
\\section{Results}
\\begin{theoremv}{T-1}[Upper bound]
Risk is small.
\\end{theoremv}
\\begin{proof}Step 1. % lean: t1_thm
\\end{proof}
`;

const BIB = parseBib(
  `@article{robins1994, title = {X}, author = {Robins}, year = {1994}\n}`,
);

function makeInput(over: Partial<HardGateInput> = {}): HardGateInput {
  const frozen = new Map(parseAnchoredEnvs(PAPER).map((e) => [e.obj_id, hashEnvBody(e.body)]));
  return {
    paperTex: PAPER,
    notation: "",
    knownObjIds: new Set(["T-1"]),
    frozenHashes: frozen,
    proofs: [{ obj_id: "T-1", proofTex: "\\begin{proof}...\\end{proof}", leanPointer: "file: x" }],
    frontMatter: "We prove a bound.",
    frozenEnvsTex: "",
    bibEntries: BIB,
    ...over,
  };
}

const passingRunners: GateRunners = {
  equivalence: async () => ({ verdict: "faithful" }),
  proofAudit: async () => ({ verdict: "faithful" }),
  overclaim: async () => ({ clean: true }),
  citationSupport: async () => ({ verdict: "supported" as const }),
};

describe("hard gates", () => {
  it("passes on a clean paper", async () => {
    expect(await runHardGates(makeInput(), passingRunners)).toEqual([]);
  });

  it("a single drift / unsupported / overclaim verdict fails the run", async () => {
    const unfaithful = await runHardGates(makeInput(), {
      ...passingRunners,
      proofAudit: async () => ({ verdict: "unfaithful", issues: ["step 2 invented"] }),
    });
    expect(unfaithful.some((p) => p.gate === "proof-audit")).toBe(true);

    const oc = await runHardGates(makeInput(), {
      ...passingRunners,
      overclaim: async () => ({ clean: false, flags: [{ sentence: "We solve everything." }] }),
    });
    expect(oc.some((p) => p.gate === "overclaim")).toBe(true);

    const cs = await runHardGates(makeInput(), {
      ...passingRunners,
      citationSupport: async () => ({ verdict: "unsupported" as const, reason: "overgeneralized" }),
    });
    expect(cs.some((p) => p.gate === "citation-support")).toBe(true);
  });

  it("flags citations outside the pool and frozen drift", async () => {
    const stray = await runHardGates(
      makeInput({ paperTex: PAPER + "\\citet{ghost2020}" }),
      passingRunners,
    );
    expect(stray.some((p) => p.gate === "cite-pool" && p.detail.includes("ghost2020"))).toBe(true);

    const drifted = await runHardGates(
      makeInput({ paperTex: PAPER.replace("Risk is small.", "Risk is tiny.") }),
      passingRunners,
    );
    expect(drifted.some((p) => p.gate === "frozen-drift")).toBe(true);
  });

  it("hard-fails when a notation-table symbol is defined after its first formal use", async () => {
    const orderPaper = PAPER + String.raw`
\begin{assumptionv}{ass:forward-axis-model}[Forward axis]
\[(X,Y)^\top=\sum_j u_jS_j.\]
\end{assumptionv}
\begin{definitionv}{def:forward-cumulant-map}[Forward map]
Let \(u_j\) be the forward loading vector.
\end{definitionv}`;
    const frozen = new Map(parseAnchoredEnvs(orderPaper).map((e) => [e.obj_id, hashEnvBody(e.body)]));
    const problems = await runHardGates(
      makeInput({
        paperTex: orderPaper,
        notation: String.raw`| forward loadings | \(u_j\) | source loading vectors | def:forward-cumulant-map |`,
        knownObjIds: new Set(["T-1", "ass:forward-axis-model", "def:forward-cumulant-map"]),
        frozenHashes: frozen,
      }),
      passingRunners,
    );
    expect(problems).toContainEqual(expect.objectContaining({
      gate: "notation-defined-after-use",
      objId: "ass:forward-axis-model",
    }));
  });
});

describe("gate loop", () => {
  it("revises until clean within the cap", async () => {
    let failures = 2;
    const r = await gateLoop({
      maxRounds: 3,
      run: async () => (failures > 0 ? [{ gate: "x", detail: "d" }] : []),
      revise: async () => {
        failures--;
      },
    });
    expect(r.ok).toBe(true);
    expect(r.rounds).toBe(2);
  });

  it("halts with problems after max rounds", async () => {
    let revisions = 0;
    const r = await gateLoop({
      maxRounds: 3,
      run: async () => [{ gate: "x", detail: "persistent" }],
      revise: async () => {
        revisions++;
      },
    });
    expect(r.ok).toBe(false);
    expect(revisions).toBe(3);
    expect(r.problems[0].detail).toBe("persistent");
  });
});

describe("helpers", () => {
  it("medianRubric takes the median of per-review means", () => {
    expect(
      medianRubric([
        { scores: { a: 2, b: 4 }, weaknesses: [] }, // 3
        { scores: { a: 8, b: 8 }, weaknesses: [] }, // 8
        { scores: { a: 6, b: 6 }, weaknesses: [] }, // 6
      ]),
    ).toBe(6);
  });

  it("parseJsonLoose finds JSON in chatter", () => {
    expect(parseJsonLoose('blah\n{"verdict": "drift"}\nbye')).toEqual({ verdict: "drift" });
    expect(parseJsonLoose(String.raw`{"verdict":"faithful","detail":"Matches \\(m\\ge1\\)."}`)).toEqual({
      verdict: "faithful",
      detail: String.raw`Matches \(m\ge1\).`,
    });
    expect(parseJsonLoose("no json")).toBeNull();
  });

  it("parseJsonLoose repairs lone LaTeX escapes without corrupting valid escaped LaTeX", () => {
    const mixed = String.raw`{"score":8.2,"issue":"valid \\(x\\)","fix":"lone \(p_k=0\)"}`;
    expect(parseJsonLoose(mixed)).toEqual({
      score: 8.2,
      issue: String.raw`valid \(x\)`,
      fix: String.raw`lone \(p_k=0\)`,
    });
  });

  it("citingSentences pairs sentences with keys", () => {
    const s = citingSentences("First fact \\citep{a1}. Second sentence. Third \\citet{b2, c3}.");
    expect(s).toHaveLength(2);
    expect(s[1].keys).toEqual(["b2", "c3"]);
  });
});

describe("parseRubricReview (P3 rubric JSON boundary)", () => {
  it("accepts a well-formed review and defaults weaknesses", () => {
    expect(parseRubricReview({ scores: { rigor: 7, novelty: 6.5 } }))
      .toEqual({ scores: { rigor: 7, novelty: 6.5 }, weaknesses: [] });
  });
  it("rejects string scores (previously became NaN and passed)", () => {
    expect(parseRubricReview({ scores: { rigor: "7/10" }, weaknesses: [] })).toBeNull();
  });
  it("rejects empty/missing scores and non-objects", () => {
    expect(parseRubricReview({ scores: {} })).toBeNull();
    expect(parseRubricReview(null)).toBeNull();
    expect(parseRubricReview({ weaknesses: ["w"] })).toBeNull();
  });
  it("rejects non-string weaknesses", () => {
    expect(parseRubricReview({ scores: { a: 5 }, weaknesses: [{ w: 1 }] })).toBeNull();
  });
  it("parseRubricReview filters legacy malformed cache entries", () => {
    const cached: unknown[] = [{ scores: { rigor: "7/10" } }, { scores: { rigor: 7 } }];
    const valid = cached.map((v) => parseRubricReview(v)).filter(Boolean);
    expect(valid).toEqual([{ scores: { rigor: 7 }, weaknesses: [] }]);
  });
});

describe("parseJsonLoose escape defense (shared with the D-stage normalizer)", () => {
  it("repairs the silent b/f/r/t collision class before parsing", () => {
    // Corpus case (panel_ppml gate cache): an under-escaped `\to` decodes to a
    // tab under plain JSON.parse; the raw-byte normalizer must restore it.
    const reply =
      "verdict follows\n" + String.raw`{"weaknesses":["type should be (\Omega_N \to \mathbb R)"]}`;
    expect(parseJsonLoose(reply)).toEqual({
      weaknesses: [String.raw`type should be (\Omega_N \to \mathbb R)`],
    });
  });

  it("repairs control characters that arrive pre-encoded as unicode escapes", () => {
    // The \u0009-channel: raw-byte normalization must preserve a valid escape,
    // so the post-parse deep repair restores the TeX command prefix.
    const reply = String.raw`{"detail":"Theorem \\ref{a} vs \u0009heta"}`;
    expect(parseJsonLoose(reply)).toEqual({
      detail: String.raw`Theorem \ref{a} vs \theta`,
    });
  });
});
