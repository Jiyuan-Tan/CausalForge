import { describe, it, expect } from "vitest";
import { parseAnchoredEnvs, lintAnchors, lintCrossRefs, lintSelfContainment, lintClarity, lintDefinitionOrder, lintNegativeContributionFraming, lintNestedMathDelimiters, lintReferences, lintHypothesisPresentation, hashEnvBody, repairObjRefs, normalizeCrefs, displaysDefiningEquality, notationHomes, usesSymbolUndecorated } from "../src/presentation/tex_anchors.js";

const TEX = `
\\section{Main results}
\\begin{assumptionv}{P-2}[Overlap tail]
The propensity tail obeys \\(c_- t^{\\kappa} \\le \\Pr(U \\le t)\\).
\\end{assumptionv}
Some prose.
\\begin{theoremv}{T-1}[Upper bound]
Risk is \\(O(n^{-(1+\\kappa)/(2+\\kappa)})\\).
\\end{theoremv}
`;

describe("notationHomes", () => {
  it("accepts both edge-piped and prompt-specified pipe-less rows", () => {
    const notation = String.raw`| note symbol | paper symbol | meaning | home |
| --- | --- | --- | --- |
| \(Q_n\) | \(Q_n\) | risk | def:risk |
\(\eta\) | \(\eta\) | treatment innovation | def:model`;
    expect(notationHomes(notation)).toEqual([
      { symbol: String.raw`Q_n`, home: "def:risk" },
      { symbol: String.raw`\eta`, home: "def:model" },
    ]);
  });
});

describe("repairObjRefs (cross-ref prefix repair + dangling-ref lint)", () => {
  const defined = new Set(["prop:oracle-regime-reduction", "thm:sharp-pointwise-lower-bound", "lem:rho-oracle-regime-algebra"]);
  it("repairs a kind-prefix-dropped ref to its unique prefixed label", () => {
    const { tex, problems } = repairObjRefs(
      "see \\ref{obj:oracle-regime-reduction} and \\ref{obj:sharp-pointwise-lower-bound}",
      defined,
    );
    expect(tex).toContain("\\ref{obj:prop:oracle-regime-reduction}");
    expect(tex).toContain("\\ref{obj:thm:sharp-pointwise-lower-bound}");
    expect(problems).toHaveLength(0);
  });
  it("leaves a correct ref and non-obj refs untouched", () => {
    const { tex, problems } = repairObjRefs("\\ref{obj:prop:oracle-regime-reduction} \\ref{eq:bound} \\ref{sec:setup}", defined);
    expect(tex).toBe("\\ref{obj:prop:oracle-regime-reduction} \\ref{eq:bound} \\ref{sec:setup}");
    expect(problems).toHaveLength(0);
  });
  it("flags a dangling obj ref that matches no defined env", () => {
    const { problems } = repairObjRefs("\\ref{obj:does-not-exist}", defined);
    expect(problems).toHaveLength(1);
    expect(problems[0].gate).toBe("undefined-ref");
  });

  it("repairs every id in a cleveref list while preserving the command", () => {
    const { tex, problems } = repairObjRefs(
      "\\Cref{obj:oracle-regime-reduction,obj:sharp-pointwise-lower-bound}",
      defined,
    );
    expect(tex).toBe("\\Cref{obj:prop:oracle-regime-reduction,obj:thm:sharp-pointwise-lower-bound}");
    expect(problems).toEqual([]);
  });
});

describe("normalizeCrefs", () => {
  it("removes manual kinds, upgrades legacy refs, and is idempotent", () => {
    const legacy = "Definition~\\ref{obj:def:risk} follows Assumption~\\autoref{obj:ass:overlap} in Equation~\\eqref{eq:risk}; see Appendix~\\cref{sec:proofs}.";
    const canonical = "\\Cref{obj:def:risk} follows \\cref{obj:ass:overlap} in \\cref{eq:risk}; see \\cref{sec:proofs}.";
    expect(normalizeCrefs(legacy)).toBe(canonical);
    expect(normalizeCrefs(canonical)).toBe(canonical);
  });

  it("unwraps reference-only inline math without touching math that contains a reference", () => {
    const source = String.raw`See \(\cref{obj:ass:low-order,obj:ass:bounded-coefficient-mass}\), then \(\Cref{obj:def:exposed-order,obj:def:minimax-risk,obj:def:model-class}\). Dollar form: $\cref{obj:thm:main}$. Keep \(x + \cref{obj:def:exposed-order}\) mathematical.`;
    const normalized = String.raw`See \cref{obj:ass:low-order,obj:ass:bounded-coefficient-mass}, then \Cref{obj:def:exposed-order,obj:def:minimax-risk,obj:def:model-class}. Dollar form: \cref{obj:thm:main}. Keep \(x + \cref{obj:def:exposed-order}\) mathematical.`;
    expect(normalizeCrefs(source)).toBe(normalized);
    expect(normalizeCrefs(normalized)).toBe(normalized);
  });

  it("keeps trailing mathematical separators around a reference inside inline math", () => {
    const source = String.raw`The constraint \(\cref{obj:ass:order} \le x\) is feasible.`;
    expect(normalizeCrefs(source)).toBe(source);
  });
});

describe("lintNestedMathDelimiters", () => {
  it("rejects inline math delimiters nested inside display math", () => {
    const bad = String.raw`\[
Q(0)\neq0,\qquad
the roots of \(Q\) are \(\{\delta,\sigma_1\}\)
\]`;
    expect(lintNestedMathDelimiters(bad)).toEqual([
      expect.objectContaining({ gate: "nested-math-delimiter" }),
    ]);
  });

  it("accepts prose with adjacent inline math and ordinary display math", () => {
    const good = String.raw`The roots of \(Q\) are \(\{\delta,\sigma_1\}\).
\[
Q(0)\neq0.
\]`;
    expect(lintNestedMathDelimiters(good)).toEqual([]);
  });

  it("accepts inline math re-entry inside text within display math", () => {
    const good = String.raw`\[
\{P:\text{\(P\) satisfies \textbf{all \(q\)-conditions above}}\}.
\]`;
    expect(lintNestedMathDelimiters(good)).toEqual([]);
  });

  it("still rejects direct nested inline math beside a text command", () => {
    const bad = String.raw`\[
\text{the following is malformed: } \(P\)
\]`;
    expect(lintNestedMathDelimiters(bad)).toEqual([
      expect.objectContaining({ gate: "nested-math-delimiter" }),
    ]);
  });

  it("rejects inline math delimiters split across distinct text arguments", () => {
    const bad = String.raw`\[\text{\(P}\quad\text{Q\)}\]`;
    expect(lintNestedMathDelimiters(bad)).toEqual([
      expect.objectContaining({ gate: "nested-math-delimiter" }),
    ]);
  });

  it("rejects an unmatched inline math opener inside text", () => {
    const bad = String.raw`\[\text{\(P}\]`;
    expect(lintNestedMathDelimiters(bad)).toEqual([
      expect.objectContaining({ gate: "nested-math-delimiter" }),
    ]);
  });

  it("rejects paragraph-column arrays that KaTeX cannot render", () => {
    const bad = String.raw`\[
\begin{array}{p{0.4\linewidth}p{0.4\linewidth}}
Reference & Result
\end{array}
\]`;
    expect(lintNestedMathDelimiters(bad)).toEqual([
      expect.objectContaining({ gate: "web-incompatible-math" }),
    ]);
  });

  it("accepts cases row-spacing syntax inside display math", () => {
    const good = String.raw`\[
x=\begin{cases}
0, & x<0,\\[1.1em]
1, & x\ge0.
\end{cases}
\]`;
    expect(lintNestedMathDelimiters(good)).toEqual([]);
  });
});

describe("tex anchors", () => {
  it("parses anchored environments", () => {
    const envs = parseAnchoredEnvs(TEX);
    expect(envs.map((e) => e.obj_id)).toEqual(["P-2", "T-1"]);
    expect(envs[1].env).toBe("theoremv");
    expect(envs[1].title).toBe("Upper bound");
    expect(envs[1].body).toContain("Risk is");
  });

  it("self-containedness: flags assumption labels with no defining env, expands ranges", () => {
    const tex = `
\\begin{theoremv}{T-5}[Converse]
Fix $P$ satisfying Assumptions A1--A4. Then the rate is sharp.
\\end{theoremv}
\\begin{theoremv}{T-4}[Achievability]
Suppose Assumption~A5 holds.
\\end{theoremv}
`;
    const labels = lintSelfContainment(tex).map((p) => p.detail);
    // A1,A2,A3,A4 (range expanded) + A5 all undefined
    expect(lintSelfContainment(tex).every((p) => p.gate === "undefined-assumption")).toBe(true);
    for (const k of ["A1", "A2", "A3", "A4", "A5"]) {
      expect(labels.some((d) => d.includes(`"${k}"`))).toBe(true);
    }
  });

  it("algorithmv is scanned as an anchored env and counts as definition-like", () => {
    const tex = `
\\begin{algorithmv}{def:est}[Estimator \\(\\hat\\theta\\)]
\\begin{enumerate}
\\item Split the sample into folds; the split satisfies (A1).
\\item Output \\[ \\hat\\theta := \\frac1K\\sum_j N_j. \\]
\\end{enumerate}
\\end{algorithmv}
\\begin{theoremv}{T-9}[Rate]
Under Assumption A1, \\(\\hat\\theta\\) of \\cref{obj:def:est} converges.
\\end{theoremv}
`;
    const envs = parseAnchoredEnvs(tex);
    expect(envs.map((e) => [e.env, e.obj_id])).toEqual([["algorithmv", "def:est"], ["theoremv", "T-9"]]);
    expect(envs[0].body).toContain("\\begin{enumerate}");
    expect(lintSelfContainment(tex)).toEqual([]); // (A1) defined inside the algorithm body
    expect(lintAnchors(tex, new Set(["def:est", "T-9"]), new Map(envs.map((e) => [e.obj_id, e.body])))).toEqual([]);
    // an algorithm is a notation home for the symbol it constructs
    const notation = "| Note symbol | Paper symbol | Meaning | Home |\n|---|---|---|---|\n| thetaHat | \\(\\hat\\theta\\) | estimator | def:est |";
    expect(lintDefinitionOrder(tex, notation)).toEqual([]);
    expect(lintDefinitionOrder(tex.replace(/^\n/, "\nEarly use of \\(\\hat\\theta\\) in a theorem: \\begin{theoremv}{T-0}[Early]\\(\\hat\\theta\\) is good.\\end{theoremv}\n"), notation)
      .some((p) => /def:est/.test(p.detail))).toBe(true);
    // a manually typed kind is caught for algorithms too
    expect(lintReferences(tex + "See Algorithm~\\cref{obj:def:est}.").some((p) => p.gate === "manual-cref-kind")).toBe(true);
  });

  it("self-containedness: passes when a definition env defines the labels", () => {
    const tex = `
\\begin{definitionv}{P-1}[Law class]
$P\\in\\mathcal P_{\\alpha,\\gamma}$ means: (A1) causal sampling; (A2) nuisance pinning;
(A3) margin; (A4) overlap decay.
\\end{definitionv}
\\begin{assumptionv}{P-7}[Achievability inputs]
The achievability condition (A5) holds.
\\end{assumptionv}
\\begin{theoremv}{T-5}[Converse]
Fix $P$ satisfying Assumptions A1--A4; on the achievability side Assumption A5 holds.
\\end{theoremv}
`;
    expect(lintSelfContainment(tex)).toEqual([]);
  });

  it("lints: bare env, unknown obj_id, frozen-body drift", () => {
    const frozen = new Map(parseAnchoredEnvs(TEX).map((e) => [e.obj_id, e.body]));
    const known = new Set(["P-2", "T-1"]);
    expect(lintAnchors(TEX, known, frozen)).toEqual([]);
    expect(
      lintAnchors(TEX + "\\begin{theorem}x\\end{theorem}", known, frozen).some(
        (p) => p.gate === "bare-env",
      ),
    ).toBe(true);
    const unknown = TEX.replace(/\{T-1\}/g, "{T-9}");
    expect(lintAnchors(unknown, known, frozen).some((p) => p.gate === "unknown-objid")).toBe(true);
    expect(lintAnchors(unknown, known, frozen).some((p) => p.gate === "not-frozen")).toBe(true);
    const drift = TEX.replace("Risk is", "Risk is at most");
    expect(lintAnchors(drift, known, frozen).some((p) => p.gate === "frozen-drift")).toBe(true);
    const reflow = TEX.replace("Risk is", "Risk\n  is");
    expect(lintAnchors(reflow, known, frozen)).toEqual([]);
  });

  it("clarity lint: flags Lean identifiers + formalization phrasing, not clean math", () => {
    // clean math notation → no problems (no false positives on real statements)
    expect(lintClarity(TEX)).toEqual([]);
    // a raw multi-word Lean decl name leaking into displayed math
    const leanId = `\\begin{lemmav}{L-9}[Pair]
The witness is \\(g_\\lambda(u) = smoothedInverseWeightRegression(a, s, \\lambda)(u)\\).
\\end{lemmav}`;
    const idProbs = lintClarity(leanId);
    expect(idProbs.some((p) => p.gate === "lean-identifier")).toBe(true);
    expect(idProbs.some((p) => p.detail.includes("smoothedInverseWeightRegression"))).toBe(true);
    const textttLeak = `\\begin{definitionv}{P-11}[Inputs]
The antecedent is represented in Lean by \\texttt{CtyDistanceIdentification}.
\\end{definitionv}`;
    const textttProblems = lintClarity(textttLeak);
    expect(textttProblems.some((p) => p.gate === "lean-identifier")).toBe(true);
    expect(textttProblems.some((p) => p.gate === "formalization-leak")).toBe(true);
    // Citation keys are intentionally identifier-shaped but are not displayed Lean names.
    expect(lintClarity(`\\begin{definitionv}{P-10}[CAD]
Classical CAD exists \\citep{BochnakCosteRoy1998,BasuPollackRoy2006}.
\\end{definitionv}`)).toEqual([]);
    // formalization-procedure / Lean-side phrasing in a statement body
    const leak = `\\begin{theoremv}{T-2}[Lower bound]
Assume the following Lean-side inputs, valid after the checks have shown membership.
\\end{theoremv}`;
    expect(lintClarity(leak).some((p) => p.gate === "formalization-leak")).toBe(true);
    // all-caps acronyms and \commands are NOT flagged
    expect(lintClarity(`\\begin{definitionv}{P-5}[Score]
The AIPW score under \\(\\mathcal{H}^\\beta\\) and \\(\\mathrm{Var}\\) is bounded.
\\end{definitionv}`)).toEqual([]);
  });

  it("clarity lint: formalization phrasing inside a PROOF block is gated too", () => {
    const proofLeak = `\\begin{proof}[Proof of \\cref{obj:thm:main}]
Lean proves the bound by unfolding the estimator. % lean: t1_thm
\\end{proof}`;
    const probs = lintClarity(proofLeak);
    expect(probs.some((p) => p.gate === "formalization-leak" && p.detail.includes("proof of thm:main"))).toBe(true);
    // the % lean: provenance tag alone is machinery, not reader-facing prose → clean
    expect(lintClarity(`\\begin{proof}[Proof of \\cref{obj:thm:main}]
By Chebyshev and the variance bound. % lean: t1_thm_variance
\\end{proof}`)).toEqual([]);
    // a NESTED claim-proof inside an outer proof is scanned as part of the outer block
    expect(lintClarity(`\\begin{proof}[Proof of \\cref{obj:thm:main}]
Step 1.
\\begin{proof}[Proof of Claim 1]
The Lean development checks this case.
\\end{proof}
Step 2.
\\end{proof}`).some((p) => p.gate === "formalization-leak")).toBe(true);
  });

  it("reference lint: cleveref contract, assumption-numbering gaps, and legacy refs", () => {
    // consecutive A-labels + target-typed cleveref references → clean
    const ok = `\\begin{assumptionv}{P-2}[Tail (A1)]Tail in \\cref{obj:P-2}.\\end{assumptionv}
\\begin{assumptionv}{P-7}[Drift (A2)]See \\cref{obj:P-4}.\\end{assumptionv}`;
    expect(lintReferences(ok)).toEqual([]);
    // a gap in A-labels (A1, A3 — missing A2)
    const gap = `\\begin{assumptionv}{P-2}[Tail (A1)]x\\end{assumptionv}
\\begin{assumptionv}{P-7}[Drift (A3)]y\\end{assumptionv}`;
    expect(lintReferences(gap).some((p) => p.gate === "assumption-numbering")).toBe(true);
    // a bare ref after a preposition (renders "…of 9")
    const bare = `\\begin{lemmav}{L-9}[Pair]The bump condition of \\ref{obj:P-12} holds.\\end{lemmav}`;
    expect(lintReferences(bare).some((p) => p.gate === "bare-ref")).toBe(true);
    // same defect with colon-prefixed semantic ids (the causalsmith default for generated labels)
    const colon = `\\begin{definitionv}{def:design-objective}[Objective]The objective $F$ is defined.\\end{definitionv}
The objective $F$ in \\ref{obj:def:design-objective} combines four terms.`;
    expect(lintReferences(colon).some((p) => p.gate === "bare-ref")).toBe(true);
    expect(lintReferences(colon).some((p) => p.gate === "legacy-ref")).toBe(true);
    expect(lintReferences("See \\ref{sec:results}.").some((p) => p.gate === "legacy-ref")).toBe(true);
    expect(lintReferences("See \\eqref{eq:result}.").some((p) => p.gate === "legacy-ref")).toBe(true);
    // a list continuation "Type~\\ref and~\\ref" is NOT a bare ref
    expect(
      lintReferences(`\\begin{theoremv}{T-1}[X]Under Assumptions~\\ref{obj:P-1} and~\\ref{obj:P-2}.\\end{theoremv}`)
        .some((p) => p.gate === "bare-ref"),
    ).toBe(false);
    // a typed reference must agree with the environment behind the obj label
    const wrongKind = `\\begin{definitionv}{def:risk}[Risk]The minimax risk.\\end{definitionv}
The setup in Section~\\ref{obj:def:risk} is finite-dimensional.`;
    expect(lintReferences(wrongKind).some((p) => p.gate === "reference-kind")).toBe(true);
    expect(lintReferences(wrongKind.replace("Section~", "Definition~")).some((p) => p.gate === "reference-kind")).toBe(false);
    expect(lintReferences(wrongKind.replace("Section~\\ref", "\\cref")).some((p) => p.gate === "legacy-ref")).toBe(false);
    expect(lintReferences(wrongKind.replace("Section~\\ref", "Definition~\\cref")).some((p) => p.gate === "manual-cref-kind")).toBe(true);
  });

  it("negative contribution framing is rejected in ordinary prose and allowed only in exempt content", () => {
    const bad = `\\begin{abstract}
This paper does not provide finite-sample inference. It is not a general identification result.
\\end{abstract}
\\begin{theoremv}{thm:a}[A result]This theorem does not require symmetry.\\end{theoremv}
\\begin{proof}The bound does not increase under truncation.\\end{proof}
\\section{Limitations and future work}
This paper does not characterize the adaptive frontier.`;
    const problems = lintNegativeContributionFraming(bad);
    expect(problems).toHaveLength(2);
    expect(problems.every((p) => p.gate === "negative-contribution-framing")).toBe(true);
    expect(problems.some((p) => p.detail.includes("finite-sample inference"))).toBe(true);
    expect(problems.some((p) => p.detail.includes("general identification"))).toBe(true);
    expect(problems.some((p) => p.detail.includes("symmetry"))).toBe(false);
    expect(problems.some((p) => p.detail.includes("adaptive frontier"))).toBe(false);
    expect(lintNegativeContributionFraming("The paper characterizes the population target under fixed overlap.")).toEqual([]);
  });

  it("rejects caveat-led and restriction-led page summaries", () => {
    const summaries = [
      "The key caveat is that exact implementability can fail under parity conditions.",
      "The main limitation is the fixed-overlap regime.",
      "These guarantees hold only under bounded graph dependence.",
      "The result is only proved for the envelope extrapolation problem.",
      "Exact schedule optimality remains an open design question.",
    ];
    for (const summary of summaries) {
      expect(lintNegativeContributionFraming(summary)).toHaveLength(1);
    }
    expect(
      lintNegativeContributionFraming(
        "Under bounded graph dependence, the design attains the conservative variance envelope.",
      ),
    ).toEqual([]);
  });

  it("hypothesis-presentation lint: flags restated assumptions + un-itemized walls, not clean statements", () => {
    // clean: a two-ref theorem stated inline is fine.
    expect(
      lintHypothesisPresentation(`\\begin{theoremv}{thm:a}[X]Under Assumptions~\\ref{obj:ass:foo} and~\\ref{obj:ass:bar}, the bound holds.\\end{theoremv}`),
    ).toEqual([]);
    // restate: a \ref'd assumption whose content is duplicated inline.
    expect(
      lintHypothesisPresentation(`\\begin{theoremv}{thm:b}[X]satisfying Assumption~\\ref{obj:ass:foo}, explicitly \\(a\\ge0\\), the bound holds.\\end{theoremv}`)
        .some((p) => p.gate === "hypothesis-restated"),
    ).toBe(true);
    // wall: many inline conditions, no itemize.
    const wall = `\\begin{theoremv}{thm:c}[X]Fix \\(\\gamma\\). Fix a regime satisfying Assumption~\\ref{obj:ass:foo}, provided \\(a\\ge0\\), such that \\(c\\ge0\\), eventually in \\(n\\).\\end{theoremv}`;
    expect(lintHypothesisPresentation(wall).some((p) => p.gate === "hypothesis-not-itemized")).toBe(true);
    // same conditions but ITEMIZED → not flagged.
    const itemized = `\\begin{theoremv}{thm:d}[X]\\begin{itemize}\\item Fix \\(\\gamma\\).\\item satisfying \\ref{obj:ass:foo}, provided \\(a\\ge0\\), such that \\(c\\ge0\\), eventually in \\(n\\).\\end{itemize}\\end{theoremv}`;
    expect(lintHypothesisPresentation(itemized).some((p) => p.gate === "hypothesis-not-itemized")).toBe(false);
  });


  it("definition-order lint: ordinary loading vectors must be defined before assumptions use them", () => {
    const notation = String.raw`
| note symbol | paper notation | defining property | home |
|---|---|---|---|
| forward loadings | \(u_j\) | forward loading vectors | def:forward-cumulant-map |
| reverse loadings | \(v_j\) | reverse loading vectors | def:reverse-cumulant-map |
| comparison relation | \(\Phi^r(\theta)=\Phi^l(\eta)\) | equality of two existing maps | def:comparison |`;
    const assumptions = String.raw`
\begin{assumptionv}{ass:forward-axis-model}[Forward axis]
\[(X,Y)^\top=\sum_{j=0}^{m+1}u_jS_j.\]
\end{assumptionv}
\begin{assumptionv}{ass:reverse-axis-model}[Reverse axis]
\[(X,Y)^\top=\sum_{j=0}^{m+1}v_jS_j.\]
\end{assumptionv}`;
    const definitions = String.raw`
\begin{definitionv}{def:forward-cumulant-map}[Forward map]
Let \(u_0=(1,\gamma)\), \(u_j=(1,\rho_j)\), and \(u_{m+1}=(0,1)\).
\end{definitionv}
\begin{definitionv}{def:reverse-cumulant-map}[Reverse map]
Let \(v_0=(1,0)\), \(v_j=(\sigma_j,1)\), and \(v_{m+1}=(\delta,1)\).
\end{definitionv}`;

    const bad = lintDefinitionOrder(assumptions + definitions, notation);
    expect(bad.map((p) => p.gate)).toEqual([
      "notation-defined-after-use",
      "notation-defined-after-use",
    ]);
    expect(bad.map((p) => p.objId)).toEqual(["ass:forward-axis-model", "ass:reverse-axis-model"]);
    expect(lintDefinitionOrder(definitions + assumptions, notation)).toEqual([]);
    expect(
      lintDefinitionOrder(
        String.raw`We define \(u_j\) as the forward source loading. ${assumptions}${definitions}`,
        notation,
      ),
    ).toHaveLength(1); // v_j remains undefined before its assumption.
  });

  it("definition-order lint collapses witnessed cycles but enforces external incoming homes", () => {
    const notation = String.raw`
| A | \(A(x)\) | first construction | a |
| B | \(B(x)\) | second construction | b |
| C | \(C(x)\) | external prerequisite | c |`;
    const cycle = String.raw`
\begin{definitionv}{a}We define \(A(x):=B(x)\).\end{definitionv}
\begin{definitionv}{b}We define \(B(x):=A(x)\).\end{definitionv}`;
    expect(lintDefinitionOrder(cycle, notation)).toEqual([]);

    const externalLate = String.raw`
\begin{definitionv}{a}We define \(A(x):=B(x)+C(x)\).\end{definitionv}
\begin{definitionv}{b}We define \(B(x):=A(x)\).\end{definitionv}
\begin{definitionv}{c}We define \(C(x):=x\).\end{definitionv>`;
    expect(lintDefinitionOrder(externalLate.replace("definitionv>", "definitionv}"), notation)).toEqual([
      expect.objectContaining({ gate: "notation-defined-after-use", objId: "a" }),
    ]);

    const internalFirstExternalSecond = String.raw`
\begin{definitionv}{b}We define \(B(x):=A(x)\).\end{definitionv}
\begin{lemmav}{external}Use \(A(x)\).\end{lemmav}
\begin{definitionv}{a}We define \(A(x):=B(x)\).\end{definitionv}`;
    expect(lintDefinitionOrder(internalFirstExternalSecond, notation)).toEqual([
      expect.objectContaining({ gate: "notation-defined-after-use", objId: "external" }),
    ]);

    const partialNotation = String.raw`| A | \(A(x)\) | first construction | a |`;
    const certifiedCycle = String.raw`
\begin{definitionv}{b}We define \(C(x):=A(x)\).\end{definitionv}
\begin{definitionv}{a}We define \(A(x):=C(x)\).\end{definitionv}`;
    expect(lintDefinitionOrder(certifiedCycle, partialNotation)).toEqual([]);
  });

  it("definition-order lint does not manufacture an edge from an unwitnessed metadata home", () => {
    const tex = String.raw`
\begin{lemmav}{use}Use \(H_n\).\end{lemmav}
\begin{definitionv}{claimed}This block does not contain the claimed notation.\end{definitionv}`;
    const notation = String.raw`| bandwidth | \(H_n\) | tuning sequence | claimed |`;
    expect(lintDefinitionOrder(tex, notation)).toEqual([]);
  });

  it("treats independently quantified local binders as scoped, but anchors later free uses", () => {
    const notation = String.raw`| size | \(M_n\) | packing size | home |`;
    const scopedBefore = String.raw`
\begin{theoremv}{other}For every \(n\), there exists an integer \(M_n\) used only in this theorem.\end{theoremv}
\begin{lemmav}{home}For every \(n\), there exists an integer \(M_n\) for the main packing.\end{lemmav}`;
    expect(lintDefinitionOrder(scopedBefore, notation)).toEqual([]);

    const freeBefore = String.raw`
\begin{theoremv}{consumer}The risk is bounded using \(M_n\).\end{theoremv}
\begin{lemmav}{home}For every \(n\), there exists an integer \(M_n\) for the main packing.\end{lemmav}`;
    expect(lintDefinitionOrder(freeBefore, notation)).toEqual([
      expect.objectContaining({ gate: "notation-defined-after-use", objId: "consumer" }),
    ]);

    const quantifiedMentionBefore = String.raw`
\begin{theoremv}{other}For every \(n\), the term \(M_n\) appears in the bound.\end{theoremv}
\begin{lemmav}{home}For every \(n\), there exists an integer \(M_n\) for the main packing.\end{lemmav}`;
    expect(lintDefinitionOrder(quantifiedMentionBefore, notation)).toEqual([
      expect.objectContaining({ gate: "notation-defined-after-use", objId: "other" }),
    ]);

    const unrelatedCueBefore = String.raw`
\begin{theoremv}{other}We define \(Q_n\) above and obtain \[M_n=0.\]\end{theoremv}
\begin{lemmav}{home}For every \(n\), there exists an integer \(M_n\) for the main packing.\end{lemmav}`;
    expect(lintDefinitionOrder(unrelatedCueBefore, notation)).toEqual([
      expect.objectContaining({ gate: "notation-defined-after-use", objId: "other" }),
    ]);
  });

  it("lints: bare obj_id in prose; \\ref{obj:...} and env bodies are exempt", () => {
    const frozen = new Map(parseAnchoredEnvs(TEX).map((e) => [e.obj_id, e.body]));
    const known = new Set(["P-2", "T-1"]);
    const leak = TEX + "\nBy Theorem~T-1 and (P-2) the bound follows.";
    const gates = lintAnchors(leak, known, frozen).filter((p) => p.gate === "objid-in-prose");
    expect(gates.map((g) => g.detail.split(" ")[0]).sort()).toEqual(["P-2", "T-1"]);
    const ok = TEX + "\nBy Theorem~\\ref{obj:T-1} and Assumption~\\ref{obj:P-2} it follows.";
    expect(lintAnchors(ok, known, frozen)).toEqual([]);
    // ids inside frozen env bodies are not prose
    expect(lintAnchors(TEX, known, frozen)).toEqual([]);
  });
});

describe("displaysDefiningEquality (reader-facing definition signal)", () => {
  // The transported-LATE regression: θ_T appeared only on the RIGHT of the Wald
  // identity and inside coverage events, so the paper never defined it.
  const buggyLayer = [
    "\\begin{theoremv}{prop:ccr}[Compact causal range]",
    "the transported first-stage mean satisfies \\[\\mu_n = P_n^F\\{D(1)=1,\\ D(0)=0\\mid S=0\\},\\]",
    "and the Wald ratio equals the target contrast, \\[\\frac{\\mu_{Y,n}}{\\mu_n}=\\theta_T.\\]",
    "Finally, \\(\\theta_T\\in\\Theta=[-1,1]\\).",
    "\\end{theoremv}",
    "\\begin{definitionv}{def:oh}[Oracle honesty]",
    "\\(\\liminf_{n\\to\\infty}\\inf_{P}P(\\theta_T\\in C_n)\\ge1-\\alpha\\).",
    "\\end{definitionv}",
  ].join("\n");
  it("RHS-only + set-membership appearances do NOT count as a definition", () => {
    expect(displaysDefiningEquality(buggyLayer, "\\theta_T")).toBe(false);
  });
  it("an LHS defining display counts", () => {
    expect(displaysDefiningEquality(buggyLayer, "\\mu_n")).toBe(true);
    expect(displaysDefiningEquality(buggyLayer, "\\Theta")).toBe(true);
    expect(
      displaysDefiningEquality("\\(\\theta_T=\\mathbb E[Y(1)-Y(0)\\mid D(1)>D(0),S=0]\\)", "\\theta_T"),
    ).toBe(true);
  });
  it("is whitespace / thin-space / script-brace insensitive", () => {
    expect(displaysDefiningEquality("\\(\\mu_{n} \\, = 3\\)", "\\mu_n")).toBe(true);
    expect(displaysDefiningEquality("\\(t_n := n\\mu_n^2/\\kappa_n\\)", "t_n")).toBe(true);
    expect(displaysDefiningEquality("\\(\\kappa_n\\coloneqq\\mathbb E_S[w^2]\\)", "\\kappa_n")).toBe(true);
    expect(displaysDefiningEquality("\\begin{align}\\theta_T &= \\mu_{Y,n}/\\mu_n\\end{align}", "\\theta_T")).toBe(true);
  });
  it("respects token boundaries", () => {
    // A decorated variant must not vouch for the base symbol, nor a longer
    // subscript for a shorter one, nor a longer command word for its prefix.
    expect(displaysDefiningEquality("\\(\\hat t_n = 1\\)", "t_n")).toBe(false);
    expect(displaysDefiningEquality("\\(\\mu_{Y,n}=1\\)", "\\mu_n")).toBe(false);
    expect(displaysDefiningEquality("\\(\\muY=1\\)", "\\mu")).toBe(false);
    expect(displaysDefiningEquality("\\(\\theta_T=1\\)", "\\theta")).toBe(false);
  });
  it("an accented LHS defines the estimator, never the base symbol (audit: one hat away)", () => {
    expect(displaysDefiningEquality("\\(\\hat\\theta_T = \\hat\\mu_{Y,n}/\\hat\\mu_n\\)", "\\theta_T")).toBe(false);
    expect(displaysDefiningEquality("\\(\\widehat\\kappa_n = 1\\)", "\\kappa_n")).toBe(false);
    expect(displaysDefiningEquality("\\(\\bar Y = 0\\)", "Y")).toBe(false);
    expect(displaysDefiningEquality("\\(\\boldsymbol\\theta_T = 1\\)", "\\theta_T")).toBe(false);
    expect(displaysDefiningEquality("\\(\\bm\\theta = 1\\)", "\\theta")).toBe(false);
    expect(displaysDefiningEquality("\\(\\mathbf\\Sigma = I\\)", "\\Sigma")).toBe(false);
  });
  it("a symbol embedded as a sub/superscript is not being defined", () => {
    expect(displaysDefiningEquality("\\(w_\\pi = 3\\)", "\\pi")).toBe(false);
    expect(displaysDefiningEquality("\\(w_{\\pi} = 3\\)", "\\pi")).toBe(false);
    expect(displaysDefiningEquality("\\(x^\\theta = 1\\)", "\\theta")).toBe(false);
  });
  it("a primed LHS defines the derived symbol, not the base", () => {
    expect(displaysDefiningEquality("\\(\\theta' = 2\\theta\\)", "\\theta")).toBe(false);
    expect(displaysDefiningEquality("\\(t_n' = 1\\)", "t_n")).toBe(false);
  });
  it("single-char script braces canonicalize beyond alphanumerics", () => {
    expect(displaysDefiningEquality("\\(\\mu^{*} := 1\\)", "\\mu^*")).toBe(true);
    expect(displaysDefiningEquality("\\(\\mu^* := 1\\)", "\\mu^{*}")).toBe(true);
  });
});

describe("node-id anchors + lintCrossRefs (graph-driven references)", () => {
  it("lintAnchors accepts graph node ids (underscored) as known obj_ids", () => {
    const tex = `\\begin{assumptionv}{a6_pcov_upper_overlap}[A6]\nThe tail is controlled.\n\\end{assumptionv}`;
    const problems = lintAnchors(tex, new Set(["a6_pcov_upper_overlap"]), null);
    expect(problems).toEqual([]);
  });

  it("flags a \\ref outside the env's edge targets (dangling)", () => {
    const layer = `\\begin{assumptionv}{a1}[A]\nUses Definition~\\ref{obj:pX}.\n\\end{assumptionv}`;
    const problems = lintCrossRefs(layer, new Map([["a1", new Set(["p7"])]]));
    expect(problems.some((p) => p.gate === "xref-dangling" && p.detail.includes("pX"))).toBe(true);
  });

  it("flags a missing reference to a declared edge target", () => {
    const layer = `\\begin{assumptionv}{a1}[A]\nNo references here.\n\\end{assumptionv}`;
    const problems = lintCrossRefs(layer, new Map([["a1", new Set(["p7"])]]));
    expect(problems.some((p) => p.gate === "xref-missing" && p.detail.includes("p7"))).toBe(true);
  });

  it("enforces (not advisory) a missing reference to an ASSUMPTION edge target", () => {
    const layer = `\\begin{theoremv}{thm:a}[A]\nNo references here.\n\\end{theoremv}`;
    // a statement-uses dep on an assumption is a hypothesis → the ENFORCED gate, not advisory xref-missing.
    const problems = lintCrossRefs(layer, new Map([["thm:a", new Set(["ass:foo", "def:bar"])]]));
    expect(problems.some((p) => p.gate === "xref-missing-assumption" && p.detail.includes("ass:foo"))).toBe(true);
    expect(problems.some((p) => p.gate === "xref-missing" && p.detail.includes("def:bar"))).toBe(true);
    // the assumption case must NOT be emitted under the advisory gate.
    expect(problems.some((p) => p.gate === "xref-missing" && p.detail.includes("ass:foo"))).toBe(false);
  });

  it("passes when refs exactly match the edge targets", () => {
    const layer = `\\begin{assumptionv}{a1}[A]\nBy Definition~\\ref{obj:p7}.\n\\end{assumptionv}`;
    expect(lintCrossRefs(layer, new Map([["a1", new Set(["p7"])]]))).toEqual([]);
  });

  it("skips an env absent from the allowed map (unconstrained)", () => {
    const layer = `\\begin{theoremv}{t9}[T]\nUses Definition~\\ref{obj:pZ}.\n\\end{theoremv}`;
    expect(lintCrossRefs(layer, new Map([["a1", new Set(["p7"])]]))).toEqual([]);
  });

  it("flags a stray ref when the env's allowed set is empty (dangling, no missing)", () => {
    const layer = `\\begin{theoremv}{t1}[T]\nStray Definition~\\ref{obj:p7}.\n\\end{theoremv}`;
    const problems = lintCrossRefs(layer, new Map([["t1", new Set<string>()]]));
    expect(problems.some((p) => p.gate === "xref-dangling" && p.detail.includes("p7"))).toBe(true);
    expect(problems.some((p) => p.gate === "xref-missing")).toBe(false);
  });
});

describe("placement and definition-order agree on decorated variants", () => {
  it("N_k^{(1)} is neither a placement user nor a first use of bare N_k", () => {
    const tex = `
\\begin{definitionv}{def:splits}[Sample splits]
The fold sizes are \\(N_k^{(1)}\\) and \\(N_{ak}^{(1)}\\).
\\end{definitionv}
\\begin{definitionv}{synth_1}[Index counts]
For an index set, \\[ N_k := |I_k|. \\]
\\end{definitionv}
`;
    const notation = "| Note symbol | Paper symbol | Meaning | Home |\n|---|---|---|---|\n| Nk | \\(N_k\\) | index count | synth_1 |";
    // The decorated split size must not read as a use of the bare symbol: if it did,
    // placement would move synth_1 later while this gate hard-failed the paper for it.
    expect(usesSymbolUndecorated("The fold sizes are \\(N_k^{(1)}\\)", "N_k")).toBe(false);
    expect(lintDefinitionOrder(tex, notation)).toEqual([]);
    // Arithmetic/operator superscripts decorate the SAME object: an early `N_k^2` is a real
    // early use and must still be caught (treating every `^` as object-forming hid these).
    for (const variant of ["N_k^2", "N_k^{-1}", "N_k^{1/2}", "N_k^\\top", "N_k^*", "N_k^{\\mathsf{T}}", "N_k^{\\mathrm{T}}"]) {
      expect(usesSymbolUndecorated(`the quantity \\(${variant}\\)`, "N_k")).toBe(true);
    }
    for (const variant of ["N_k^{(1)}", "N_k^{\\mathrm{loc}}"]) {
      expect(usesSymbolUndecorated(`the quantity \\(${variant}\\)`, "N_k")).toBe(false);
    }
    expect(
      lintDefinitionOrder(tex.replace("The fold sizes are", "The square \\(N_k^2\\) and the fold sizes are"), notation)
        .some((p) => /synth_1/.test(p.detail)),
    ).toBe(true);
    // A genuinely early BARE use is still caught.
    const early = tex.replace("The fold sizes are", "The count \\(N_k\\) and the fold sizes are");
    expect(lintDefinitionOrder(early, notation).some((p) => /synth_1/.test(p.detail))).toBe(true);
  });
});
