import { describe, it, expect } from "vitest";
import { parseAnchoredEnvs, lintAnchors, lintCrossRefs, lintSelfContainment, lintClarity, lintDefinitionOrder, lintNegativeContributionFraming, lintNestedMathDelimiters, lintReferences, lintHypothesisPresentation, lintNotation, hashEnvBody, texSafeTitle, repairObjRefs, normalizeCrefs, estimatorNotationFamily, estimatorNotationFamilies, sameEstimatorNotationFamily } from "../src/presentation/tex_anchors.js";

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
  it("groups cosmetic selected-estimator variants without merging distinct estimators", () => {
    expect(estimatorNotationFamily(String.raw`Selected estimator \(\widehat\tau^{\mathrm{sel}}_{C_\epsilon,\epsilon}\)`))
      .toBe(String.raw`\widehat\tau:sel`);
    expect(sameEstimatorNotationFamily(
      String.raw`\widehat\tau_{\mathrm{sel}}`,
      String.raw`\widehat\tau^{\mathrm{sel}}_{C_\epsilon,\epsilon}`,
    )).toBe(true);
    expect(sameEstimatorNotationFamily(
      String.raw`\widehat\tau_{\mathrm{sel}}`,
      String.raw`\widehat\tau_{\mathrm{ctr}}`,
    )).toBe(false);
    expect(estimatorNotationFamily(String.raw`\widehat\tau_n`)).toBeNull();
    const definingStatement = String.raw`Define \(\widehat\tau^{\mathrm{sel}}_{C_\epsilon,\epsilon}\) to be \(\widehat\tau_n^{\mathrm{hyb}}\) in one branch and \(\widehat\tau_{\mathrm{ctr}}\) otherwise.`;
    expect(estimatorNotationFamilies(definingStatement)).toEqual([
      String.raw`\widehat\tau:sel`,
      String.raw`\widehat\tau:hyb`,
      String.raw`\widehat\tau:ctr`,
    ]);
    expect(sameEstimatorNotationFamily(definingStatement, String.raw`\widehat\tau_{\mathrm{sel}}`)).toBe(true);
  });
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
    const frozen = new Map(parseAnchoredEnvs(TEX).map((e) => [e.obj_id, hashEnvBody(e.body)]));
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

  it("notation lint: parameterized class needs a definition; bare space + defined class are fine", () => {
    // \mathcal{H}^\beta(...) used in a statement, no defining env → flagged
    const undef = `\\begin{assumptionv}{P-13}[Closure]The profile $g_1\\in\\mathcal{H}^{\\beta}(C_\\beta;[0,t_0])$.\\end{assumptionv}`;
    const probs = lintNotation(undef);
    expect(probs.some((p) => p.gate === "notation-undefined" && p.detail.includes("\\mathcal{H}"))).toBe(true);
    // a definitionv whose TITLE names the class → resolved
    const defd = `\\begin{definitionv}{P-10}[The class $\\mathcal{P}_{\\kappa,\\beta,n}$]Members are laws.\\end{definitionv}
\\begin{theoremv}{T-2}[Lower]Some $Q\\in\\mathcal{P}_{\\kappa,\\beta,n}$ forces the rate.\\end{theoremv}`;
    expect(lintNotation(defd)).toEqual([]);
    // a bare ambient space \mathcal{X} (no parameters) is NOT checked
    expect(lintNotation(`\\begin{theoremv}{T-1}[X]For $X:\\Omega\\to\\mathcal{X}$ the rate holds.\\end{theoremv}`)).toEqual([]);
  });

  it("notation lint: matches bare/spaced \\mathcal H too (the Hölder-ball miss)", () => {
    // unbraced `\mathcal H^\beta` used in a statement, no defining env → flagged
    const undef = `\\begin{assumptionv}{P-13}[Closure]The profile $g_1\\in\\mathcal H^{\\beta}(L_\\beta)$.\\end{assumptionv}`;
    const probs = lintNotation(undef);
    expect(probs.some((p) => p.gate === "notation-undefined" && p.detail.includes("\\mathcal{H}"))).toBe(true);
    // a braced def `\mathcal{P}` covers a bare use `\mathcal P` (same symbol)
    const mixed = `\\begin{definitionv}{P-10}[The class $\\mathcal{P}_{\\kappa,\\beta,n}$]Members are laws.\\end{definitionv}
\\begin{theoremv}{T-2}[Lower]Some $Q\\in\\mathcal P_{\\kappa,\\beta,n}$ forces the rate.\\end{theoremv}`;
    expect(lintNotation(mixed)).toEqual([]);
  });

  it("notation lint: recognizes a sentence-initial synthesized class definition", () => {
    const tex = `\\begin{definitionv}{synth_1}We say \\(\\mathcal P_N\\) is the triangular-array sampling law when it supplies the displayed expectations.\\end{definitionv}
\\begin{assumptionv}{A-1}For every law \\(\\mathcal P_N\\), the mean restriction holds.\\end{assumptionv}`;
    expect(lintNotation(tex)).toEqual([]);
  });

  it("notation lint: other class fonts (\\mathfrak/\\mathscr), not \\mathbb/\\mathrm", () => {
    // \mathfrak class used, undefined → flagged
    expect(lintNotation(`\\begin{lemmav}{L-1}[X]The σ-field $\\mathfrak F_{n}$ refines.\\end{lemmav}`)
      .some((p) => p.detail.includes("\\mathfrak{F}"))).toBe(true);
    // \mathbb is standard sets — a parameterized \mathbb E must NOT be flagged here
    // (the codex notation check owns \mathbb/\mathrm with its standard-symbol excludes)
    expect(lintNotation(`\\begin{theoremv}{T-1}[X]The mean $\\mathbb E_{H_n}[U]$ is finite.\\end{theoremv}`)).toEqual([]);
  });

  it("notation lint: treats the standard normal law as standard mathematics", () => {
    expect(
      lintNotation(
        `\\begin{lemmav}{L-1}[CLT]For every $s\\in\\mathbb R$, $\\Pr(S_n\\le s)\\to\\Pr(Z\\le s)$, where $Z\\sim\\mathcal N(0,1)$.\\end{lemmav}`,
      ),
    ).toEqual([]);

    // A genuinely parameterized calligraphic-N object remains protected by the orphan detector.
    expect(
      lintNotation(`\\begin{theoremv}{T-1}[Neighbourhood]The set $\\mathcal N_i$ is finite.\\end{theoremv}`)
        .some((p) => p.gate === "notation-undefined" && p.detail.includes("\\mathcal{N}")),
    ).toBe(true);
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

  it("lints: bare obj_id in prose; \\ref{obj:...} and env bodies are exempt", () => {
    const frozen = new Map(parseAnchoredEnvs(TEX).map((e) => [e.obj_id, hashEnvBody(e.body)]));
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

describe("texSafeTitle", () => {
  it("transliterates Unicode, wraps backtick spans in math, drops pipeline fragments", () => {
    expect(texSafeTitle("Rate frontier `\u03c1_n(\u03ba, \u03b2)`")).toBe(
      "Rate frontier $\\rho _n(\\kappa, \\beta)$",
    );
    expect(texSafeTitle("Triangular-array class `\ud835\udcab_{\u03ba,\u03b2,n}`")).toBe(
      "Triangular-array class $\\mathcal{P}_{\\kappa,\\beta,n}$",
    );
    expect(texSafeTitle("One-sided tail (P-form of A2)")).toBe("One-sided tail (A2)");
    expect(texSafeTitle("Perturbability (P-form of A6, .tex 470\u2013479)")).toBe("Perturbability (A6)");
    // a span already carrying $...$ keeps its own math mode
    expect(texSafeTitle("Envelope at `$\\lambda_n^\\dagger$`")).toBe("Envelope at $\\lambda_n^\\dagger$");
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
