import { describe, expect, it } from "vitest";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { spawnSync } from "node:child_process";
import os from "node:os";
import path from "node:path";
import { renderCoreTex } from "../../src/discovery/core/render_tex.js";
import { alignedRowTerminatorViolations, repairSerializedLatex } from "../../src/discovery/core/latex_serialization.js";
import { CoreSchema, type Core } from "../../src/discovery/core/schema.js";

function golden(): Core {
  return CoreSchema.parse(
    JSON.parse(
      readFileSync(new URL("../fixtures/stat_ate_overlap_decay_proto_core.json", import.meta.url), "utf8"),
    ),
  );
}

describe("renderCoreTex (deterministic core → .tex)", () => {
  it("renders a complete document from the proposal core: prose + formal nodes", () => {
    const tex = renderCoreTex(golden());
    // structure
    expect(tex).toContain("\\begin{document}");
    expect(tex).toContain("\\end{document}");
    // prose fields
    expect(tex).toContain("TL;DR");
    expect(tex).toContain("Project justification");
    expect(tex).toContain("\\paragraph{Gap.}");
    expect(tex).toContain("\\section{Related work}");
    expect(tex).toContain("Primary functional / estimator / diagnostic:");
    expect(tex).not.toContain("Identifying functional / recovery map:");
    // formal nodes, each labelled by id
    expect(tex).toContain("\\label{ass:tail}");
    expect(tex).toContain("\\label{thm:lower}");
    expect(tex).toContain("\\begin{conjecture}");
    // per-statement prose rendered
    expect(tex).toContain("\\textit{Justification.}");
    expect(tex).toContain("\\textit{Consumer.}");
  });

  it("loads a broad, ordered compatibility preamble for LLM-authored LaTeX", () => {
    const tex = renderCoreTex(golden());
    expect(tex).toContain("\\usepackage{amsmath,amssymb,amsthm,mathtools}");
    expect(tex).toContain("\\usepackage{mathrsfs,bm,bbm}");
    expect(tex).toContain("\\usepackage{graphicx,booktabs,array,multirow,tabularx,longtable}");
    expect(tex).toContain("\\usepackage[numbers,sort&compress]{natbib}");
    expect(tex).toContain("\\usepackage{cleveref}");
    expect(tex.indexOf("{natbib}")).toBeLessThan(tex.indexOf("hyperref"));
    expect(tex.indexOf("hyperref")).toBeLessThan(tex.indexOf("\\usepackage{cleveref}"));
  });

  it("is a pure function — same core renders identically", () => {
    expect(renderCoreTex(golden())).toBe(renderCoreTex(golden()));
  });

  it("escapes qid/spec metadata and repairs recurrent authored-string serialization hazards", () => {
    const core = CoreSchema.parse({
      ...golden(),
      qid: "exp_interference",
      specialization: "holder_eprocess",
      tldr: "The raw pi_exp token is text.\\n\\[x_1 \\le x_2\\]",
    });
    const tex = renderCoreTex(core);
    expect(tex).toContain("\\usepackage[margin=0.8in]{geometry}");
    expect(tex).toContain("\\section*{exp\\_\\allowbreak{}interference}");
    expect(tex).toContain("\\noindent\\textit{Specialization:} holder\\_\\allowbreak{}eprocess\\par");
    expect(tex).toContain("raw pi\\_exp token");
    expect(tex).toContain("text.\n\\[x_1 \\le x_2\\]");
  });

  it("preserves TeX not-equal/not-in commands and aligned row breaks", () => {
    const corruptedNotEqual = "For \\(k" + "\n" + "e j\\), \\(a" + "\n" + "otin\\mathcal H_n\\).";
    const corruptedRowBreak = "\\[\\begin{aligned}a&=b" + "\\" + "\n&=c.\\end{aligned}\\]";
    const core = CoreSchema.parse({
      ...golden(),
      statements: golden().statements.map((s, i) => i === 0 ? {
        ...s,
        statement: corruptedNotEqual,
        proof_tex: corruptedRowBreak,
      } : s),
    });
    const tex = renderCoreTex(core);
    expect(tex).toContain("k\\ne j");
    expect(tex).toContain("a\\notin\\mathcal H_n");
    expect(tex).toContain("a&=b\\\\\n&=c");
  });

  it("repairs a literal serialized newline before whitespace in authored LaTeX", () => {
    const core = CoreSchema.parse({
      ...golden(),
      statements: golden().statements.map((s, i) => i === 0 ? {
        ...s,
        proof_tex: "First display:\\[\\n q_i=Q_i/\\sum_jQ_j.\\]",
      } : s),
    });
    const tex = renderCoreTex(core);
    expect(tex).toContain("First display:\\[\n q_i=Q_i/\\sum_jQ_j.\\]");
    expect(tex).not.toContain("\\[\\n q_i");
  });

  it("repairs serialized newlines after display delimiters before lowercase tokens", () => {
    const core = CoreSchema.parse({
      ...golden(),
      statements: golden().statements.map((statement, index) => index === 0 ? {
        ...statement,
        proof_tex: String.raw`\[\np_+=1.\]\nand hence\[\nq=2.\] The command \nu is preserved.`,
      } : statement),
    });
    const tex = renderCoreTex(core);
    expect(tex).toContain("\\[\np_+=1.\\]\nand hence\\[\nq=2.\\]");
    expect(tex).toContain(String.raw`The command \nu is preserved.`);
    expect(tex).not.toContain(String.raw`\[\np_+`);
    expect(tex).not.toContain(String.raw`\]\nand hence`);
  });

  it("repairs JSON-over-escaped authored LaTeX without changing legitimate line breaks", () => {
    const doubled = String.raw`\\(\\pi_{ij}\\)`;
    const core = CoreSchema.parse({
      ...golden(),
      symbols: golden().symbols.map((symbol, index) => index === 0
        ? { ...symbol, name: doubled, def: String.raw`the \\(j\\)-th coordinate of \\(\\pi_i\\)` }
        : symbol),
      tldr: String.raw`A doubled delimiter \\(x\\) followed by a real \\ line break.`,
    });
    const tex = renderCoreTex(core);
    expect(tex).toContain(String.raw`\item \(\pi_{ij}\)`);
    expect(tex).toContain(String.raw`the \(j\)-th coordinate of \(\pi_i\)`);
    expect(tex).toContain(String.raw`a real \\ line break`);
    expect(tex).not.toContain(String.raw`\\(`);
  });

  it("does not de-double a lone row break before a parenthesis (no over-escape evidence)", () => {
    // Audit finding: a string whose ONLY backslashes are a `\\` row break directly
    // before "(" must not be reinterpreted as a doubled inline-math opener. The
    // collapse requires positive whole-string evidence: paired doubled delimiters
    // or a doubled command.
    const rowBreak = String.raw`First line\\(second line)`;
    expect(repairSerializedLatex(rowBreak)).toBe(rowBreak);
  });

  it("preserves a cases row break immediately followed by a parenthesized expression", () => {
    const proof = String.raw`\[H_i=\begin{cases}A_iY_i,&d=\mathrm{PN},\\(1-A_i)(1-Y_i),&d=\mathrm{PS}.\end{cases}\]`;
    const repaired = repairSerializedLatex(proof);
    expect(repaired).toContain(String.raw`,\\(1-A_i)`);
    expect(repaired).not.toContain(String.raw`,\(1-A_i)`);

    const core = CoreSchema.parse({
      ...golden(),
      statements: golden().statements.map((statement, index) => index === 0
        ? { ...statement, proof_tex: proof }
        : statement),
    });
    expect(renderCoreTex(core)).toContain(String.raw`,\\(1-A_i)`);
  });

  it("repairs an under-escaped forall in a legacy formal field without emitting control bytes", () => {
    const corruptedForall = "H_{F,n}:Y_{ij}(1)=Y_{ij}(0)\\ " + "\f" + "orall(i,j)";
    const core = CoreSchema.parse({ ...golden(), target_estimand: corruptedForall });
    const tex = renderCoreTex(core);
    expect(tex).toContain("\\textbackslash{}\\allowbreak{}forall(i,\\allowbreak{}j)");
    expect([...tex].filter((ch) => ch.charCodeAt(0) < 32 && !["\t", "\n", "\r"].includes(ch))).toEqual([]);
  });

  it("restores any control character before a letter to its TeX command prefix", () => {
    const corrupted = "See \\(\t" + "exttt{def:pair-action}\\) and \\(\t" + "ext{orbit}\\).";
    expect(repairSerializedLatex(corrupted)).toBe(
      String.raw`See \(\texttt{def:pair-action}\) and \(\text{orbit}\).`,
    );
    // Authored control characters are forbidden in pipeline text, so a tab before
    // a letter is unambiguously a lost TeX backslash under that invariant...
    expect(repairSerializedLatex("left\tright")).toBe(String.raw`left\tright`);
    // ...while a control character NOT before a letter is left alone and fails
    // closed at the model-boundary backstop.
    expect(repairSerializedLatex("left\t right")).toBe("left\t right");
  });

  it("repairs v-family TeX commands decoded to vertical tabs", () => {
    const corrupted = "If \\(\\mathcal H=" + "\v" + "arnothing\\), set " +
      "\v" + "arepsilon_0=" + "\v" + "arepsilon_1.";
    expect(repairSerializedLatex(corrupted)).toBe(
      String.raw`If \(\mathcal H=\varnothing\), set \varepsilon_0=\varepsilon_1.`,
    );
  });

  it("canonicalizes every aligned row terminator to exactly two backslashes", () => {
    const malformed = [
      "\\begin{aligned}",
      `a&=b${"\\".repeat(3)}`,
      `&=c${"\\".repeat(4)}`,
      `&=d${"\\".repeat(5)}`,
      "&=e",
      "\\end{aligned}",
    ].join("\n");
    const repaired = repairSerializedLatex(malformed);
    expect(alignedRowTerminatorViolations(repaired)).toEqual([]);
    const counts = repaired.split("\n").map((line) => line.match(/(\\+)$/)?.[1].length).filter(Boolean);
    expect(counts).toEqual([2, 2, 2]);
  });

  it("adapts legacy formal DSL fields without rewriting explicitly authored LaTeX", () => {
    const core = CoreSchema.parse({
      ...golden(),
      target_estimand: "theta=n^{-1}sum_i Y_i",
      assumptions: golden().assumptions.map((a, i) => i === 0 ? { ...a, condition: "P_Z=product_i Bernoulli(p_i)" } : a),
      statements: golden().statements.map((s, i) => i === 0
        ? { ...s, statement: "For every m in M_n, theta_hat=theta" }
        : i === 1 ? { ...s, statement: "For every \\(m\\in\\mathcal M_n\\), \\widehat\\theta=\\theta." } : s),
    });
    const tex = renderCoreTex(core);
    expect(tex).toContain("\\texttt{theta=\\allowbreak{}n");
    expect(tex).toContain("\\texttt{P\\_\\allowbreak{}Z=\\allowbreak{}product");
    expect(tex).toContain("For every m in M\\_\\allowbreak{}n");
    expect(tex).toContain("For every \\(m\\in\\mathcal M_n\\), \\widehat\\theta=\\theta.");
  });

  it("renders legacy symbol spaces/signatures through the formal adapter and compiles", () => {
    const core = CoreSchema.parse({
      qid: "exp_symbol_contract",
      specialization: "v1_sig",
      cluster: "experimentation",
      target_estimand: "\\(\\theta\\)",
      estimand_functional: "\\(\\widehat\\theta\\)",
      symbols: [
        { name: "Z", type: "assignment_vector", space: "{0,1}^n", role: "random_assignment" },
        { name: "c_i", type: "exposure_map", sig: "{0,1}^{N_i} -> E_n", role: "known_map" },
        { name: "pi_exp", type: "positivity_constant", space: "R_+", role: "lower_bound" },
        { name: "h", type: "other_exposure", space: "E_n\\{a,b}", role: "remainder" },
      ],
      assumptions: [{
        id: "ass:positive", condition: "\\(0<\\pi_{\\exp}\\)", free_symbols: ["pi_exp"],
        standard: { name: "positivity", cite: "Ref" },
      }],
      definitions: [],
      statements: [{
        id: "thm:identity", kind: "theorem", statement: "\\(1=1\\).", depends_on: [], status: "proved",
        proof_tex: "\\begin{proof}Immediate.\\end{proof}",
      }, {
        id: "thm:long-layout", kind: "theorem",
        statement: "The oracle identity is \\(\\beta_{n,\\mathrm{rep}}^\\star(\\alpha;Q,\\Gamma)=\\mathbb E_{q^{\\otimes n}}[\\mathbf 1\\{n^{-1}\\sum_{i=1}^n s_\\Gamma(Z_i)>\\Delta(Q,\\Gamma)/2\\}]\\). Moreover, \\[\\sup_{p_1,\\ldots,p_n\\in\\mathcal P_m(\\Gamma)}\\mathbb E_{\\otimes_{i=1}^np_i}[\\phi_n(Z)]\\le e^{-c_0(Q,\\Gamma)n},\\qquad\\mathbb E_{q^{\\otimes n}}[1-\\phi_n(Z)]\\le e^{-c_0(Q,\\Gamma)n}.\\]",
        depends_on: [], status: "proved", proof_tex: "\\begin{proof}Immediate.\\end{proof}",
        gap: "The \\(\\texttt{stat_rosenbaum_lf_family_minimax}\\) substrate.",
      }],
      bibliography: [
        { key: "RefA", citation: "Statistics & Probability Letters" },
        { key: "RefB", citation: "Random Structures & Algorithms" },
      ],
      tldr: "A renderer contract test.",
      project_justification: { gap: "Test gap.", niche: "Test niche.", fill: "Test fill." },
      related_work: "The script family \\(\\mathscr{F}\\) follows \\citet{RefA}.",
    });
    const tex = renderCoreTex(core);
    expect(tex).toContain("\\texttt{\\{0,\\allowbreak{}1\\}\\allowbreak{}");
    expect(tex).toContain("\\texttt{R\\_\\allowbreak{}+\\allowbreak{}");
    expect(tex).toContain("\\texttt{E\\_\\allowbreak{}n\\textbackslash{}\\allowbreak{}");
    expect(tex).toContain("N\\_\\allowbreak{}i\\}\\allowbreak{} -\\allowbreak{}> E\\_\\allowbreak{}n");
    expect(tex).toContain("Statistics \\& Probability Letters");
    expect(tex).toContain("Random Structures \\& Algorithms");
    expect(tex).toContain("\\mathscr{F}");
    expect(tex).toContain("\\citet{RefA}");
    expect(tex).toContain("\\texttt{stat\\_rosenbaum\\_lf\\_family\\_minimax}");
    expect(tex).toContain("\\resizebox{0.98\\linewidth}");

    const available = spawnSync("pdflatex", ["--version"], { encoding: "utf8" });
    if (available.error) return;
    const dir = mkdtempSync(path.join(os.tmpdir(), "causalsmith-render-test-"));
    try {
      const file = path.join(dir, "writeup.tex");
      writeFileSync(file, tex, "utf8");
      for (let pass = 1; pass <= 2; pass++) {
        const compiled = spawnSync(
          "pdflatex",
          ["-interaction=nonstopmode", "-halt-on-error", `-output-directory=${dir}`, file],
          { encoding: "utf8" },
        );
        expect(`${compiled.stdout}\n${compiled.stderr}`, `${compiled.stdout}\n${compiled.stderr}`).toBeTruthy();
        expect(compiled.status, `pdflatex pass ${pass}:\n${compiled.stdout}\n${compiled.stderr}`).toBe(0);
      }
      const log = readFileSync(path.join(dir, "writeup.log"), "utf8");
      expect(log).not.toContain("Overfull \\hbox");
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it("preserves authored bibliography LaTeX while escaping raw prose ampersands", () => {
    const core = CoreSchema.parse({
      ...golden(),
      bibliography: [{ key: "RefA", citation: "Author (2026). \\emph{Methods & Practice}." }],
    });
    const tex = renderCoreTex(core);
    expect(tex).toContain("\\emph{Methods \\& Practice}");
    expect(tex).not.toContain("\\textbackslash{}emph");
  });

  it("repairs a bibliography math delimiter missing the final math-command brace", () => {
    const core = CoreSchema.parse({
      ...golden(),
      bibliography: [{ key: "RefA", citation: "Author. DOI \\(10.1093/\\mathrm{ectj}/\\mathrm{utac002\\)." }],
    });
    const tex = renderCoreTex(core);
    expect(tex).toContain("DOI \\(10.1093/\\mathrm{ectj}/\\mathrm{utac002}\\).");
  });

  it("a standard assumption renders its cite; the witness construction renders inputs", () => {
    const tex = renderCoreTex(golden());
    expect(tex).toContain("\\cite{Tsybakov2009}");
    expect(tex).toContain("\\begin{definition}");
  });

  it("round-trips and renders a technical limitation as an unnumbered diagnostic", () => {
    const diagnostic =
      "For this template only, P_+^n(D_n=-)=e^{-n C_*}K_{+,n}; this is not a SCORE impossibility theorem.";
    const core = CoreSchema.parse({ ...golden(), technical_internal_limitation: diagnostic });

    expect(core.technical_internal_limitation).toBe(diagnostic);
    const tex = renderCoreTex(core);
    expect(tex).toContain("\\section*{Technical internal limitation (diagnostic only)}");
    // `_` and `^` are both math-mode-only; in undelimited text both are escaped
    // (a raw `^` would abort pdflatex with "Missing $ inserted").
    expect(tex).toContain(
      "P\\_+\\textasciicircum{}n(D\\_n=-)=e\\textasciicircum{}{-n C\\_*}K\\_{+,n}",
    );
    expect(tex).not.toContain("\\begin{theorem}[technical_internal_limitation]");
  });
});
