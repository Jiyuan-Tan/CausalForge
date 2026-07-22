import { describe, expect, it, vi } from "vitest";
import { existsSync, mkdtempSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  loadLibrary,
  libraryRoot,
  statementHash,
  reviewStatus,
  declArea,
  declPagePath,
  isTier1,
  linkifyStatement,
  firstSentence,
  publicAxioms,
  buildModuleTree,
  displayModulePath,
  displayModuleSegment,
  sourceKind,
} from "../src/lib/library.js";

function trackedLeanFiles(root: string): string[] {
  try {
    return execFileSync("git", ["ls-files", "Causalean/**/*.lean"], {
      cwd: root,
      encoding: "utf8",
    })
      .split(/\r?\n/)
      .filter((file) => file && existsSync(join(root, file)));
  } catch (err) {
    const out =
      err && typeof err === "object" && "stdout" in err && typeof err.stdout === "string"
        ? err.stdout
        : "";
    if (!out) throw err;
    return out.split(/\r?\n/).filter((file) => file && existsSync(join(root, file)));
  }
}

function fixtureRoot(opts: { badReviewDecl?: boolean; malformedSidecar?: boolean } = {}): string {
  const root = mkdtempSync(join(tmpdir(), "libsite-"));
  mkdirSync(join(root, "doc", "library_review"), { recursive: true });
  const entries = [
    {
      name: "Causalean.PO.Foo",
      kind: "def",
      module: "Causalean.PO.Basic",
      file: "Causalean/PO/Basic.lean",
      line: 10,
      statement: "ℕ →  ℕ",
      doc: "Adds one.\n\nNote.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      name: "Causalean.Graph.Bar",
      kind: "theorem",
      module: "Causalean.Graph.Basic",
      file: "Causalean/Graph/Basic.lean",
      line: 5,
      statement: "∀ n, Foo n = n + 1",
      doc: null,
      refs: ["Causalean.PO.Foo"],
      axioms: ["sorryAx"],
      usesSorry: true,
    },
    {
      // A structure field whose leaf name is a single letter. A bare `W` in
      // another statement is a bound variable, not a reference to this field.
      name: "Causalean.PO.System.W",
      kind: "def",
      module: "Causalean.PO.Basic",
      file: "Causalean/PO/Basic.lean",
      line: 20,
      statement: "ℝ",
      doc: null,
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      name: "Causalean.Substrate.Temp.helper",
      kind: "def",
      module: "Causalean.Substrate.Temp.Basic",
      file: "Causalean/Substrate/Temp/Basic.lean",
      line: 1,
      statement: "Nat",
      doc: "Temporary study-mode substrate helper.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
  ];
  writeFileSync(
    join(root, "doc", "library_index.json"),
    JSON.stringify({
      commit: "abc",
      toolchain: "t",
      entries,
      modules: {
        "Causalean.PO.Basic": "Core PO helpers.",
        "Causalean.Substrate.Temp.Basic": "Temporary study-mode substrate helpers.",
      },
    }),
  );
  writeFileSync(
    join(root, "doc", "library_review", "PO.json"),
    JSON.stringify({
      // A non-array `reviews` is STRUCTURAL corruption (hard error); a dangling
      // decl name is mere DRIFT (warn-and-drop).
      headline_theorems: [],
      reviews: opts.malformedSidecar
        ? ({} as unknown[])
        : [
            {
              decl: opts.badReviewDecl ? "Causalean.PO.Nope" : "Causalean.PO.Foo",
              statement_hash: statementHash("ℕ → ℕ"),
              reviewed_at_commit: "abc",
              reviewer: "j",
            },
          ],
      flags: [],
    }),
  );
  return root;
}

describe("site library loader", () => {
  it("loads, areas, tiers, statuses", () => {
    const lib = loadLibrary(fixtureRoot());
    const foo = lib.entries.find((e) => e.name === "Causalean.PO.Foo")!;
    expect(declArea(foo)).toBe("PO");
    expect(isTier1(foo, lib.sidecars)).toBe(true);
    expect(reviewStatus(foo, lib.sidecars)).toBe("reviewed");
  });
  it("excludes study-mode substrate declarations and modules from the public Causalean page", () => {
    const lib = loadLibrary(fixtureRoot());
    expect(lib.entries.map((e) => e.name)).not.toContain("Causalean.Substrate.Temp.helper");
    expect(Object.keys(lib.modules)).not.toContain("Causalean.Substrate.Temp.Basic");
  });
  it("renders the DiscreteID module segment as Discrete ID", () => {
    expect(displayModuleSegment("DiscreteID")).toBe("Discrete ID");
    expect(displayModulePath("ID.DiscreteID")).toBe("ID.Discrete ID");
  });
  it("adds discretionary hyphen breaks to long CamelCase module labels", () => {
    expect(displayModuleSegment("ResidualQuadratic")).toBe(
      "Residual\u00adQuadratic",
    );
    expect(displayModuleSegment("BoundedOutcomeEnvelope")).toBe(
      "Bounded\u00adOutcome\u00adEnvelope",
    );
  });
  it("directory cards wrap long submodule names within their tile", () => {
    const css = readFileSync(join(libraryRoot(), "CausalSmith", "site", "src", "styles", "library.css"), "utf8");
    expect(css).toMatch(/\.dir-card\s*\{[^}]*min-width:\s*0\b/s);
    expect(css).toMatch(/\.dir-card \.module-name\s*\{[^}]*overflow-wrap:\s*anywhere\b/s);
  });
  it("directory cards in the grid stretch to equal row height", () => {
    const css = readFileSync(join(libraryRoot(), "CausalSmith", "site", "src", "styles", "library.css"), "utf8");
    expect(css).toMatch(/\.dir-list\.grid\s*\{[^}]*align-items:\s*stretch\b/s);
    expect(css).toMatch(/\.dir-list\.grid\s*\{[^}]*grid-auto-rows:\s*1fr\s*;/s);
    expect(css).toMatch(/\.dir-list\.grid \.dir-card\s*\{[^}]*height:\s*100%\s*;/s);
    expect(css).toMatch(/\.dir-card\s*\{[^}]*box-sizing:\s*border-box\s*;/s);
  });
  it("directory cards stay compact while using available brief space", () => {
    const css = readFileSync(join(libraryRoot(), "CausalSmith", "site", "src", "styles", "library.css"), "utf8");
    const page = readFileSync(join(libraryRoot(), "CausalSmith", "site", "src", "pages", "library", "[...slug].astro"), "utf8");
    expect(css).toMatch(/\.dir-card\s*\{[^}]*gap:\s*0\.05rem\s*;[^}]*padding:\s*0\.45rem 0\.65rem\s*;/s);
    expect(css).toMatch(/\.dir-card \.module-brief\s*\{[^}]*--dir-brief-lines:\s*3\s*;/s);
    expect(css).toMatch(/\.dir-list\.grid \.dir-card \.module-brief\s*\{[^}]*-webkit-line-clamp:\s*var\(--dir-brief-lines\)\s*;/s);
    expect(css).toMatch(/\.dir-list\.grid \.dir-card \.module-brief\s*\{[^}]*line-clamp:\s*var\(--dir-brief-lines\)\s*;/s);
    expect(page).toContain("fitDirectoryCardBriefs");
    expect(page).toContain("--dir-brief-lines");
  });
  it("CausalSmith Working Papers masthead uses a single intro divider", () => {
    const css = readFileSync(join(libraryRoot(), "CausalSmith", "site", "src", "styles", "series.css"), "utf8");
    expect(css).toMatch(/\.masthead\s*\{[^}]*border-bottom:\s*1px solid var\(--rule\)\s*;/s);
    expect(css).not.toMatch(/\.masthead\s*\{[^}]*border-bottom:\s*[^;]*double\b/s);
  });
  it("wraps short library statements while keeping multi-line statements scrollable", () => {
    const root = libraryRoot();
    const component = readFileSync(join(root, "CausalSmith", "site", "src", "components", "ModuleNode.astro"), "utf8");
    const css = readFileSync(join(root, "CausalSmith", "site", "src", "styles", "library.css"), "utf8");
    const page = readFileSync(join(root, "CausalSmith", "site", "src", "pages", "library", "[...slug].astro"), "utf8");
    expect(component).toContain('text.split("\\n").length < 5 ? "decl-stmt-wrap" : "decl-stmt-scrollable"');
    expect(component).toContain("const theoremStmtClass");
    // Depth-aware, not a naive `/\s:=/` search: a named-argument application
    // inside the signature itself (`H_ε (γ := γ) ε`) must not be mistaken for
    // the real proof-start marker and truncate the signature mid-binder.
    expect(component).toContain("const proofStart = findProofStart(source);");
    expect(css).toMatch(/\.decl-stmt-wrap\s*\{[^}]*white-space:\s*pre-wrap\s*;/s);
    expect(css).toMatch(/\.decl-stmt-scrollable\s*\{[^}]*overflow-x:\s*auto\s*;/s);
    expect(page).toContain('block.classList.contains("decl-stmt-scrollable")');
  });
  it("published library areas have a table intro", () => {
    const lib = loadLibrary(libraryRoot());
    const areas = [...new Set(lib.entries.map(declArea))].sort();
    const missing = areas.filter((area) => !(lib.sidecars[area]?.intro ?? "").trim());
    expect(missing).toEqual([]);
  });
  it("published PO and Panel area intros match their current scope", () => {
    const lib = loadLibrary(libraryRoot());
    const poIntro = lib.sidecars.PO?.intro ?? "";
    const panelIntro = lib.sidecars.Panel?.intro ?? "";

    expect(poIntro).toContain("Standard potential-outcome framework");
    expect(poIntro).not.toMatch(/potential-outcome calculus/i);
    expect(panelIntro).toContain("Panel-data causal econometrics");
    expect(panelIntro).not.toMatch(/panel-question grammar/i);
  });
  it("published namespace pages have short descriptions", () => {
    const lib = loadLibrary(libraryRoot());
    const areas = [...new Set(lib.entries.map(declArea))].sort();
    const missing: string[] = [];
    const visit = (area: string, node: ReturnType<typeof buildModuleTree>[number]) => {
      if (node.children.length > 0) {
        const intro =
          lib.sidecars[area]?.namespace_intros?.[node.path] ??
          firstSentence(lib.modules[`Causalean.${area}.${node.path}`] ?? null);
        if (!(intro ?? "").trim()) missing.push(`${area}.${node.path}`);
      }
      node.children.forEach((child) => visit(area, child));
    };
    for (const area of areas) {
      const modules = [
        ...new Set(lib.entries.filter((entry) => declArea(entry) === area).map((entry) => entry.module)),
      ];
      buildModuleTree(area, modules).forEach((node) => visit(area, node));
    }
    expect(missing).toEqual([]);
  });
  it("published review sidecars do not contain stale decl references", () => {
    const root = libraryRoot();
    const lib = loadLibrary(root);
    const names = new Set(lib.entries.map((e) => e.name));
    const reviewDir = join(root, "doc", "library_review");
    const stale: string[] = [];
    const duplicateHeadlines: string[] = [];
    for (const file of readdirSync(reviewDir).filter((f) => f.endsWith(".json"))) {
      const sidecar = JSON.parse(readFileSync(join(reviewDir, file), "utf8")) as {
        headline_theorems: string[];
        reviews: { decl: string }[];
        flags: { decl: string }[];
      };
      const seen = new Set<string>();
      for (const decl of sidecar.headline_theorems) {
        if (!names.has(decl)) stale.push(`${file}: headline ${decl}`);
        if (seen.has(decl)) duplicateHeadlines.push(`${file}: ${decl}`);
        seen.add(decl);
      }
      for (const review of sidecar.reviews) {
        if (!names.has(review.decl)) stale.push(`${file}: review ${review.decl}`);
      }
      for (const flag of sidecar.flags) {
        if (!names.has(flag.decl)) stale.push(`${file}: flag ${flag.decl}`);
      }
    }
    expect(stale).toEqual([]);
    expect(duplicateHeadlines).toEqual([]);
  });
  it("published page annotations resolve flagged internal wording", () => {
    const lib = loadLibrary(libraryRoot());
    const entries = new Map(lib.entries.map((entry) => [entry.name, entry]));
    const docsWithoutInternalLabels = [
      "Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.bridge_Dtilde_sq_eq_VD",
      "Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.bridge_VD_pos_iff_Dtilde_sq_pos",
      "Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.bridge_finite_residualized_eq_twfe",
      "Causalean.SCM.Examples.ContinuousBackdoor.cb_backdoor_identified",
      "Causalean.SCM.obsKernel_fixSet_W_rect_integral_eq",
    ];
    for (const name of docsWithoutInternalLabels) {
      const doc = entries.get(name)?.doc ?? "";
      expect(doc, name).not.toMatch(/\b(?:B\d+|G\d+|Helper\s+\d+)\b|reusability check/i);
    }
    for (const entry of lib.entries.filter((entry) => entry.file.startsWith("Causalean/SCM/Do/Rule2Kernel/"))) {
      expect(entry.doc ?? "", entry.name).not.toMatch(/\bHelper\s+\d+\b/);
    }

    const activeFlags = Object.values(lib.sidecars)
      .flatMap((sidecar) => sidecar.flags ?? [])
      .map((flag) => `${flag.decl}: ${flag.note}`);
    expect(
      activeFlags.filter((flag) =>
        /Bxx|Gxxx|reusability check|Helper 3|hdealine|not curated/i.test(flag),
      ),
    ).toEqual([]);
  });
  it("published PO and Experimentation curation resolves flagged headline gaps", () => {
    const lib = loadLibrary(libraryRoot());
    const entries = new Map(lib.entries.map((entry) => [entry.name, entry]));
    const expected = [
      "Causalean.PO.ID.Exact.VariableIntensityIV.VariableIntensityIVSystem.SpecialCases.wald_eq_marginResponseAverage",
      "Causalean.Experimentation.TwoStageInterference.wald_coverage_feasible",
    ];
    for (const name of expected) {
      const decl = entries.get(name);
      expect(decl, name).toBeDefined();
      expect(isTier1(decl!, lib.sidecars), name).toBe(true);
    }
  });
  it("published pages with theorem declarations have a curated theorem card", () => {
    const lib = loadLibrary(libraryRoot());
    const pages = new Map<string, { theorems: number; curatedTheorems: number }>();
    for (const entry of lib.entries) {
      const page = declPagePath(entry, lib);
      const rec = pages.get(page) ?? { theorems: 0, curatedTheorems: 0 };
      if (["theorem", "lemma"].includes(entry.kind)) {
        rec.theorems += 1;
        if (isTier1(entry, lib.sidecars)) rec.curatedTheorems += 1;
      }
      pages.set(page, rec);
    }
    const pagesWithoutCuratedTheorem = [...pages]
      .filter(([, counts]) => counts.theorems > 0 && counts.curatedTheorems === 0)
      .map(([page]) => page)
      .sort();
    expect(pagesWithoutCuratedTheorem).toEqual([]);
  });
  it("published SCM theorem modules have curated theorem anchors", () => {
    const lib = loadLibrary(libraryRoot());
    const modules = new Map<string, { theorems: number; curatedTheorems: number }>();
    for (const entry of lib.entries) {
      if (!entry.file.startsWith("Causalean/SCM/")) continue;
      if (!["theorem", "lemma"].includes(entry.kind)) continue;
      const rec = modules.get(entry.module) ?? { theorems: 0, curatedTheorems: 0 };
      rec.theorems += 1;
      if (isTier1(entry, lib.sidecars)) rec.curatedTheorems += 1;
      modules.set(entry.module, rec);
    }
    const modulesWithoutCuratedTheorem = [...modules]
      .filter(([, counts]) => counts.theorems > 0 && counts.curatedTheorems === 0)
      .map(([module]) => module)
      .sort();
    expect(modulesWithoutCuratedTheorem).toEqual([]);
  });
  it("publishes the monotone counterfactual bound as an SCM example", () => {
    const lib = loadLibrary(libraryRoot());
    const staleEntries = lib.entries
      .filter(
        (entry) =>
          entry.name.startsWith("Causalean.SCM.ID.Flagship.") ||
          entry.module.startsWith("Causalean.SCM.ID.Flagship.") ||
          entry.file.startsWith("Causalean/SCM/ID/Flagship/"),
      )
      .map((entry) => entry.name)
      .sort();
    const staleSidecarKeys = Object.keys(lib.sidecars.SCM?.namespace_intros ?? {}).filter((path) =>
      path.startsWith("ID.Flagship"),
    );

    expect(staleEntries).toEqual([]);
    expect(staleSidecarKeys).toEqual([]);
    expect(
      lib.entries.some(
        (entry) =>
          entry.name ===
            "Causalean.SCM.Examples.MonotoneCounterfactualBound.monotoneCounterfactualBound" &&
          entry.module === "Causalean.SCM.Examples.MonotoneCounterfactualBound" &&
          entry.file === "Causalean/SCM/Examples/MonotoneCounterfactualBound.lean",
      ),
    ).toBe(true);
  });
  it("published PO MSM cutoff calibration theorems are curated", () => {
    const lib = loadLibrary(libraryRoot());
    const expected = [
      "Causalean.PO.POBackdoorSystem.wMin_mul_propScore_le_one",
      "Causalean.PO.POBackdoorSystem.one_le_wMax_mul_propScore",
      "Causalean.PO.POBackdoorSystem.condExp_treat_wMin_eq",
      "Causalean.PO.POBackdoorSystem.condExp_treat_wMax_eq",
      "Causalean.PO.POBackdoorSystem.wMin0_mul_propScore_le_one",
      "Causalean.PO.POBackdoorSystem.one_le_wMax0_mul_propScore",
      "Causalean.PO.POBackdoorSystem.condExp_control_wMin0_eq",
      "Causalean.PO.POBackdoorSystem.condExp_control_wMax0_eq",
      "Causalean.PO.POBackdoorSystem.control_calibValue_eq",
      "Causalean.PO.POBackdoorSystem.controlCutoffProp_calibrated_of_survival",
      "Causalean.PO.POBackdoorSystem.cutoffProp0_mem_MSMSet0",
      "Causalean.PO.POBackdoorSystem.cutoffProp0_mem_MSMSetCalib0_of_survival",
    ];
    for (const name of expected) {
      const decl = lib.entries.find((entry) => entry.name === name);
      expect(decl, name).toBeDefined();
      expect(isTier1(decl!, lib.sidecars), name).toBe(true);
    }
  });
  it("published LiNGAM namespace has a page intro", () => {
    const lib = loadLibrary(libraryRoot());
    const intro =
      lib.sidecars.Discovery?.namespace_intros?.LiNGAM ??
      firstSentence(lib.modules["Causalean.Discovery.LiNGAM"] ?? null);
    expect((intro ?? "").trim()).not.toBe("");
  });
  it("published PLR namespace has a page intro", () => {
    const lib = loadLibrary(libraryRoot());
    const intro =
      lib.sidecars.Estimation?.namespace_intros?.PLR ??
      firstSentence(lib.modules["Causalean.Estimation.PLR"] ?? null);
    expect((intro ?? "").trim()).not.toBe("");
  });
  it("published MinimaxATE causal namespace has a page intro", () => {
    const lib = loadLibrary(libraryRoot());
    const intro =
      lib.sidecars.Estimation?.namespace_intros?.["MinimaxATE.Causal"] ??
      firstSentence(lib.modules["Causalean.Estimation.MinimaxATE.Causal"] ?? null);
    expect((intro ?? "").trim()).not.toBe("");
  });
  it("published Mathlib Probability namespace pages have intros", () => {
    const lib = loadLibrary(libraryRoot());
    const paths = ["Probability", "Probability.Kernel", "Probability.SteinMethod"];
    const missing = paths.filter((path) => {
      const intro =
        lib.sidecars.Mathlib?.namespace_intros?.[path] ??
        firstSentence(lib.modules[`Causalean.Mathlib.${path}`] ?? null);
      return !(intro ?? "").trim();
    });
    expect(missing).toEqual([]);
  });
  it("does not treat generated native_decide witnesses as public axioms", () => {
    const axioms = [
      "sorryAx",
      "Causalean.Estimation.MinimaxATE.Causal.wSWIGGraph._native.native_decide.ax_1",
      "Causalean.Foo.some_real_axiom",
    ];
    expect(publicAxioms(axioms)).toEqual(["Causalean.Foo.some_real_axiom"]);
  });
  it("published LiNGAM core theorems are curated", () => {
    const lib = loadLibrary(libraryRoot());
    const core = [
      "Causalean.Discovery.LiNGAM.colSupport_of_kurtosis",
      "Causalean.Discovery.LiNGAM.ica_genPerm_relation",
      "Causalean.Discovery.LiNGAM.lingam_identifiable",
      "Causalean.Discovery.LiNGAM.lingam_identifiability_kurtosis",
    ];
    const entries = new Map(lib.entries.map((e) => [e.name, e]));
    expect(core.filter((name) => !entries.has(name))).toEqual([]);
    expect(core.filter((name) => !isTier1(entries.get(name)!, lib.sidecars))).toEqual([]);
  });
  it("published Discovery main theorems are curated", () => {
    const lib = loadLibrary(libraryRoot());
    const core = [
      "Causalean.Discovery.LiNGAM.colSupport_of_kurtosis",
      "Causalean.Discovery.LiNGAM.ica_genPerm_relation",
      "Causalean.Discovery.LiNGAM.lingam_identifiable",
      "Causalean.Discovery.LiNGAM.lingam_identifiability_kurtosis",
      "Causalean.Discovery.LinearDisentanglement.sigma_solutions",
      "Causalean.Discovery.LinearDisentanglement.disentanglement_uniqueness",
      "Causalean.Discovery.LinearDisentanglement.disentanglement_identifiability",
      "Causalean.Discovery.InvariantPrediction.EnvFamily.mechanism_invariant",
      "Causalean.Discovery.InvariantPrediction.EnvFamily.icp_sound",
      "Causalean.Discovery.InvariantPrediction.LinearGaussian.EnvFamily.icp_complete_linearGaussian",
    ];
    const entries = new Map(lib.entries.map((e) => [e.name, e]));
    expect(core.filter((name) => !entries.has(name))).toEqual([]);
    expect(core.filter((name) => !isTier1(entries.get(name)!, lib.sidecars))).toEqual([]);
  });
  it("published Mathlib monomial-matrix helpers are curated", () => {
    const lib = loadLibrary(libraryRoot());
    const core = [
      "Causalean.Mathlib.LinearAlgebra.perm_uniqueness",
      "Causalean.Mathlib.LinearAlgebra.genPerm_of_invertible_of_colSupport",
      "Causalean.Mathlib.LinearAlgebra.eq_of_genPerm_triangular_unitDiag",
    ];
    const entries = new Map(lib.entries.map((e) => [e.name, e]));
    expect(core.filter((name) => !entries.has(name))).toEqual([]);
    expect(core.filter((name) => !isTier1(entries.get(name)!, lib.sidecars))).toEqual([]);
  });
  it("published Causalean source files are represented in the library index", () => {
    const root = libraryRoot();
    const lib = loadLibrary(root);
    const leanFiles = trackedLeanFiles(root);
    const entryFiles = new Set(lib.entries.map((entry) => entry.file));
    const moduleFiles = new Set(
      Object.keys(lib.modules).map((module) => `${module.replace(/\./g, "/")}.lean`),
    );
    const missing = leanFiles
      .filter((file) => !entryFiles.has(file) && !moduleFiles.has(file))
      .sort();

    expect(missing).toEqual([]);
  });
  it("published Mathlib theorem modules have curated theorem anchors", () => {
    const lib = loadLibrary(libraryRoot());
    const modules = new Map<string, { theorems: number; curatedTheorems: number }>();
    for (const entry of lib.entries) {
      if (!entry.file.startsWith("Causalean/Mathlib/")) continue;
      if (!["theorem", "lemma"].includes(entry.kind)) continue;
      const rec = modules.get(entry.module) ?? { theorems: 0, curatedTheorems: 0 };
      rec.theorems += 1;
      if (isTier1(entry, lib.sidecars)) rec.curatedTheorems += 1;
      modules.set(entry.module, rec);
    }
    const modulesWithoutCuratedTheorem = [...modules]
      .filter(([, counts]) => counts.theorems > 0 && counts.curatedTheorems === 0)
      .map(([module]) => module)
      .sort();
    expect(modulesWithoutCuratedTheorem).toEqual([]);
  });
  it("published Experimentation paper-level theorems are curated", () => {
    const lib = loadLibrary(libraryRoot());
    const core = [
      "Causalean.Experimentation.DesignBased.E_htTotal",
      "Causalean.Experimentation.DesignBased.E_htMean",
      "Causalean.Experimentation.DesignBased.E_htEffect",
      "Causalean.Experimentation.DesignBased.Var_htTotal_cov",
      "Causalean.Experimentation.DesignBased.Var_htTotal",
      "Causalean.Experimentation.DesignBased.Cov_htTotal_cov",
      "Causalean.Experimentation.DesignBased.Cov_htTotal",
      "Causalean.Experimentation.DesignBased.FiniteDesign.chebyshev",
      "Causalean.Experimentation.DesignBased.FiniteDesign.var_edge_sum_le",
      "Causalean.Experimentation.DesignBased.FiniteDesign.Var_compound_eq_tower",
      "Causalean.Experimentation.DesignBased.FiniteDesign.Var_prod_linear_comb",
      "Causalean.Experimentation.DesignBased.prodDesign_toMeasure_eq_pi",
      "Causalean.Experimentation.DesignBased.indepFun_prodDesign_blocks",
      "Causalean.Experimentation.DesignBased.prodDesign_clt",
      "Causalean.Experimentation.ExposureMappingInterference.E_htVarEst",
      "Causalean.Experimentation.ExposureMappingInterference.E_htVarEst_eq_addBias",
      "Causalean.Experimentation.ExposureMappingInterference.E_htVarEst_add_htA2_ge",
      "Causalean.Experimentation.ExposureMappingInterference.E_htCovEst_le",
      "Causalean.Experimentation.ExposureMappingInterference.E_htCovEst_eq_of_noEffect",
      "Causalean.Experimentation.ExposureMappingInterference.E_htCovEstA_le",
      "Causalean.Experimentation.ExposureMappingInterference.E_htEffectVarEst_ge",
      "Causalean.Experimentation.ExposureMappingInterference.E_htEffectVarEstA_ge",
      "Causalean.Experimentation.ExposureMappingInterference.wald_coverage",
      "Causalean.Experimentation.ExposureMappingInterference.wald_coverage_feasible",
      "Causalean.Experimentation.ExposureMappingInterference.wald_coverage_feasible_of_relVar",
      "Causalean.Experimentation.ExposureMappingInterference.localDependenceCLT_of_stein",
      "Causalean.Experimentation.ExposureMappingInterference.localDependenceCLT_of_conditions",
      "Causalean.Experimentation.ExposureMappingInterference.localDependenceCLT_of_paper_conditions",
      "Causalean.Experimentation.ExposureMappingInterference.var_htEdgeStat_le",
      "Causalean.Experimentation.ExposureMappingInterference.htEffectVarEst_undershoot_tendsto_zero",
      "Causalean.Experimentation.TwoStageInterference.E_groupEst",
      "Causalean.Experimentation.TwoStageInterference.E_popEst",
      "Causalean.Experimentation.TwoStageInterference.E_popEst_pick",
      "Causalean.Experimentation.TwoStageInterference.E_ShatTreated",
      "Causalean.Experimentation.TwoStageInterference.E_ShatControl",
      "Causalean.Experimentation.TwoStageInterference.Var_groupAgg",
      "Causalean.Experimentation.TwoStageInterference.Var_srs_mean",
      "Causalean.Experimentation.TwoStageInterference.LHExperiment.E_estD",
      "Causalean.Experimentation.TwoStageInterference.LHExperiment.var_estD",
      "Causalean.Experimentation.TwoStageInterference.varHat_nonneg",
      "Causalean.Experimentation.UnknownInterference.E_htSummand",
      "Causalean.Experimentation.UnknownInterference.SAHExperiment.D_E_htEst",
      "Causalean.Experimentation.UnknownInterference.SAHExperiment.D_Var_htEst_le",
      "Causalean.Experimentation.UnknownInterference.SAHExperiment.chebyshev_eate",
      "Causalean.Experimentation.UnknownInterference.chebyshev_ci_eate",
      "Causalean.Experimentation.UnknownInterference.var_htSummand_le",
      "Causalean.Experimentation.UnknownInterference.cov_htSummand_zero",
    ];
    const entries = new Map(lib.entries.map((e) => [e.name, e]));
    expect(core.filter((name) => !entries.has(name))).toEqual([]);
    expect(core.filter((name) => !isTier1(entries.get(name)!, lib.sidecars))).toEqual([]);
  });
  it("published Experimentation theorem modules have curated theorem anchors", () => {
    const lib = loadLibrary(libraryRoot());
    const modules = new Map<string, { theorems: number; curatedTheorems: number }>();
    for (const entry of lib.entries) {
      if (!entry.file.startsWith("Causalean/Experimentation/")) continue;
      if (!["theorem", "lemma"].includes(entry.kind)) continue;
      const rec = modules.get(entry.module) ?? { theorems: 0, curatedTheorems: 0 };
      rec.theorems += 1;
      if (isTier1(entry, lib.sidecars)) rec.curatedTheorems += 1;
      modules.set(entry.module, rec);
    }
    const modulesWithoutCuratedTheorem = [...modules]
      .filter(([, counts]) => counts.theorems > 0 && counts.curatedTheorems === 0)
      .map(([module]) => module)
      .sort();
    expect(modulesWithoutCuratedTheorem).toEqual([]);
  });
  it("published Stat Matrix design-inverse theorems are curated", () => {
    const lib = loadLibrary(libraryRoot());
    const core = [
      "Causalean.Stat.Concentration.designInv00_perturb",
      "Causalean.Stat.Concentration.iid_sum_union_bound",
      "Causalean.Stat.Concentration.designMatrix_inv_concentration",
    ];
    const entries = new Map(lib.entries.map((e) => [e.name, e]));
    expect(core.filter((name) => !entries.has(name))).toEqual([]);
    expect(core.filter((name) => !isTier1(entries.get(name)!, lib.sidecars))).toEqual([]);
  });
  it("published Stat minimax testing theorems are curated", () => {
    const lib = loadLibrary(libraryRoot());
    const core = [
      "Causalean.Stat.bretagnolle_huber_affinity",
      "Causalean.Stat.Minimax.leCam_two_point_L1_lower",
      "Causalean.Stat.Minimax.le_cam_two_point_mse",
      "Causalean.Stat.le_cam_two_point_chisq",
      "Causalean.Stat.mixtureReal_le",
    ];
    const entries = new Map(lib.entries.map((e) => [e.name, e]));
    expect(core.filter((name) => !entries.has(name))).toEqual([]);
    expect(core.filter((name) => !isTier1(entries.get(name)!, lib.sidecars))).toEqual([]);
  });
  it("published Stat second-moment and equicontinuity modules have curated anchors", () => {
    const lib = loadLibrary(libraryRoot());
    const modules = [
      "Causalean.Stat.CLT.SecondMomentOperator",
      "Causalean.Stat.EmpiricalProcess.Equicontinuity.Process",
      "Causalean.Stat.EmpiricalProcess.Equicontinuity.SecondMoment",
    ];
    const modulesWithoutHeadline = modules.filter((module) =>
      lib.entries
        .filter((entry) => entry.module === module && ["theorem", "lemma"].includes(entry.kind))
        .every((entry) => !isTier1(entry, lib.sidecars)),
    );
    expect(modulesWithoutHeadline).toEqual([]);
  });
  it("published Stat OrderM theorem modules have curated theorem anchors", () => {
    const lib = loadLibrary(libraryRoot());
    const modules = new Map<string, { theorems: number; curatedTheorems: number }>();
    for (const entry of lib.entries) {
      if (!entry.module.startsWith("Causalean.Stat.UStatistic.OrderM")) continue;
      if (!["theorem", "lemma"].includes(entry.kind)) continue;
      const rec = modules.get(entry.module) ?? { theorems: 0, curatedTheorems: 0 };
      rec.theorems += 1;
      if (isTier1(entry, lib.sidecars)) rec.curatedTheorems += 1;
      modules.set(entry.module, rec);
    }
    const modulesWithoutHeadline = [...modules]
      .filter(([, counts]) => counts.theorems > 0 && counts.curatedTheorems === 0)
      .map(([module]) => module)
      .sort();
    expect(modulesWithoutHeadline).toEqual([]);
  });
  it("published Stat theorem modules have curated theorem anchors", () => {
    const lib = loadLibrary(libraryRoot());
    const modules = new Map<string, { theorems: number; curatedTheorems: number }>();
    for (const entry of lib.entries) {
      if (!entry.file.startsWith("Causalean/Stat/")) continue;
      if (!["theorem", "lemma"].includes(entry.kind)) continue;
      const rec = modules.get(entry.module) ?? { theorems: 0, curatedTheorems: 0 };
      rec.theorems += 1;
      if (isTier1(entry, lib.sidecars)) rec.curatedTheorems += 1;
      modules.set(entry.module, rec);
    }
    const modulesWithoutHeadline = [...modules]
      .filter(([, counts]) => counts.theorems > 0 && counts.curatedTheorems === 0)
      .map(([module]) => module)
      .sort();
    expect(modulesWithoutHeadline).toEqual([]);
  });
  it("published Stat file modules have short descriptions", () => {
    const lib = loadLibrary(libraryRoot());
    const area = "Stat";
    const modules = [
      ...new Set(lib.entries.filter((entry) => entry.file.startsWith("Causalean/Stat/")).map((entry) => entry.module)),
    ];
    const missing: string[] = [];
    const visit = (node: ReturnType<typeof buildModuleTree>[number]) => {
      const modDoc = node.module ? (lib.modules[node.module] ?? null) : null;
      const nsIntro = lib.sidecars[area]?.namespace_intros?.[node.path] ?? null;
      const brief = firstSentence(modDoc) ?? nsIntro;
      if (node.children.length === 0 && !(brief ?? "").trim()) {
        missing.push(node.module ?? `Causalean.${area}.${node.path}`);
      }
      node.children.forEach(visit);
    };
    buildModuleTree(area, modules).forEach(visit);
    expect(missing.sort()).toEqual([]);
  });
  it("published Estimation theorem modules have curated theorem anchors", () => {
    const lib = loadLibrary(libraryRoot());
    const modules = [
      "Causalean.Estimation.ATE.Score.ScorePullout",
      "Causalean.Estimation.ATT.Score.ScorePullout",
      "Causalean.Estimation.DTR.ScorePullout",
      "Causalean.Estimation.DTR.Constructor",
      "Causalean.Estimation.DTR.RemainderIdentity.Helpers",
      "Causalean.Estimation.DTR.ScoreL2.Helpers",
      "Causalean.Estimation.DTR.SeqDRMoment",
      "Causalean.Estimation.CATE.Core.PhiEtaDeriv",
      "Causalean.Estimation.CATE.Kennedy.DRLearner",
      "Causalean.Estimation.MinimaxATE.ConstCenterHalf.Construction",
      "Causalean.Estimation.MinimaxATE.ConstCenterHalf.Gap",
      "Causalean.Estimation.MinimaxATE.ConstCenterHalf.Membership",
      "Causalean.Estimation.MinimaxATE.ConstCenterHalf.ChiSqOverlap",
      "Causalean.Estimation.MinimaxATE.ConstCenterGeneral.Construction",
      "Causalean.Estimation.MinimaxATE.ConstCenterGeneral.Gap",
      "Causalean.Estimation.MinimaxATE.ConstCenterGeneral.Membership",
      "Causalean.Estimation.MinimaxATE.ConstCenterGeneral.ChiSqOverlap",
      "Causalean.Estimation.MinimaxATE.Reduction.Bump",
      "Causalean.Estimation.MinimaxATE.Causal.Construction",
      "Causalean.Estimation.MinimaxATE.VaryingCenterCase1.Construction",
      "Causalean.Estimation.MinimaxATE.VaryingCenterCase1.Gap",
      "Causalean.Estimation.MinimaxATE.VaryingCenterCase1.Membership",
      "Causalean.Estimation.MinimaxATE.VaryingCenterCase1.ChiSqOverlap",
      "Causalean.Estimation.MinimaxATE.VaryingCenterCase2.Construction",
      "Causalean.Estimation.MinimaxATE.VaryingCenterCase2.Gap",
      "Causalean.Estimation.MinimaxATE.VaryingCenterCase2.Membership",
      "Causalean.Estimation.MinimaxATE.VaryingCenterCase2.ChiSqOverlap",
      "Causalean.Estimation.NPIV.Operator.Adjoint",
      "Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.Algebra",
      "Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.EPPerN",
      "Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.LocalizedEventF",
      "Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.LocalizedEventH",
      "Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.Regulariser",
      "Causalean.Estimation.OrthogonalMoments.LinearSmoother",
      "Causalean.Estimation.OrthogonalMoments.MomentFunctional",
      "Causalean.Estimation.OrthogonalMoments.NeymanOrthogonal",
      "Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.RandomParam",
      "Causalean.Estimation.OrthogonalLearning.Sparse.Setup",
      "Causalean.Estimation.PLR.Moment",
      "Causalean.Estimation.PLR.Setup",
    ];
    const modulesWithoutHeadline = modules.filter((module) =>
      lib.entries
        .filter((entry) => entry.module === module && ["theorem", "lemma"].includes(entry.kind))
        .every((entry) => !isTier1(entry, lib.sidecars)),
    );
    expect(modulesWithoutHeadline).toEqual([]);
  });
  it("published module-level support anchors are curated", () => {
    const lib = loadLibrary(libraryRoot());
    const core = [
      "Causalean.Estimation.ATE.BackdoorEstimationSystem.aipw_mean_zero",
      "Causalean.Estimation.ATE.BackdoorEstimationSystem.aipw_finite_var",
      "Causalean.Estimation.ATT.TreatedEstimationSystem.aipw_mean_zero_ATT",
      "Causalean.Estimation.DTR.DTREstimationSystem.seqDR_mean_zero",
      "Causalean.Estimation.MinimaxATE.nMiss_sq_le_nMSE",
      "Causalean.Discovery.LinearDisentanglement.key_identity",
      "Causalean.Experimentation.DesignBased.exists_isOptimalOn",
      "Causalean.Experimentation.TwoStageInterference.E_Shat",
      "Causalean.Experimentation.TwoStageInterference.DEbar_eq_of_homogeneous",
      "Causalean.Mathlib.InformationTheory.entropy_le_log_card",
      "Causalean.Mathlib.InformationTheory.fano_inequality",
      "Causalean.Mathlib.InformationTheory.gaussianKL_eq",
      "Causalean.Mathlib.Probability.bernoulli_mean_channel_kl",
      "Causalean.Estimation.OrthogonalMoments.smoother_bias_holder",
      "Causalean.Estimation.OrthogonalMoments.smoother_bias_product_holder",
      "Causalean.Estimation.ATE.BackdoorEstimationSystem.weighted_residual_integral_zero",
      "Causalean.Estimation.ATT.TreatedEstimationSystem.weighted_residual_false_integral_zero",
      "Causalean.Estimation.DTR.DTREstimationSystem.weighted_residual_integral_zero_stage0",
      "Causalean.Estimation.DTR.DTREstimationSystem.indicator_to_propScore_integral_stage1",
      "Causalean.Estimation.CATE.phi_eta_dir_deriv_tendsto",
      "Causalean.Estimation.MinimaxATE.inClass_perturbed",
      "Causalean.Estimation.MinimaxATE.GenConstr.inClassG",
      "Causalean.Estimation.MinimaxATE.VarConstr.inClassV",
      "Causalean.Estimation.MinimaxATE.VarConstr2.inClass2",
      "Causalean.Estimation.NPIV.Primal.ep_inequality_from_localized",
      "Causalean.Estimation.OrthogonalLearning.randomParam_event_le",
      "Causalean.Estimation.Efficiency.hasDerivAt_tiltExp",
      "Causalean.Estimation.PLR.PLRSystem.plr_meanZero",
      "Causalean.PO.POBalkePearlSystem.ATE_eq_sum_latent",
      "Causalean.PO.POBackdoorSystem.cutoff_optimal0",
      "Causalean.PO.POBackdoorSystem.msmUpperCalib0_eq_cutoff",
      "Causalean.PO.POBackdoorSystem.msmLowerCalib0_eq_cutoff",
      "Causalean.PO.PODynLATESystem.cCompliance_bridge",
      "Causalean.PO.POProximalSystem.condMeanYofA_W_mem_Icc",
      "Causalean.PO.POProximalSystem.condIntYofA_eq_hq_armSwap_twoProxy",
      "Causalean.PO.RDDLimits.oneSidedLimit_eq_left",
      "Causalean.Discovery.LinearDisentanglement.porq_exists",
      "Causalean.Discovery.LinearDisentanglement.porq_unique",
      "Causalean.Discovery.LinearDisentanglement.rowspan_inclusion_a",
      "Causalean.Experimentation.DesignBased.FiniteDesign.mse_eq_var_add_bias_sq",
      "Causalean.Experimentation.TwoStageInterference.exists_strat_factor",
      "Causalean.PartialID.RandomSet.supportFn_minkowskiMean",
      "Causalean.PartialID.supportFn_add_dir_le",
      "Causalean.SCM.ancestralFactorization",
      "Causalean.SCM.obsCondIndep_contraction",
      "Causalean.SCM.exists_evalMap_overrideC_factors_cutset",
      "Causalean.SCM.cutsetLatent_dSep_of_dSep",
      "Causalean.SCM.obsDensity_eq_qFactorDensityProduct",
      "Causalean.SCM.qFactorDensityProduct_eq_prod_cComponentFactor",
      "Causalean.SCM.obsKernel_map_eq_obsCondKernel_comp",
      "Causalean.Stat.Concentration.criticalRadius_fp_of_subRoot",
      "Causalean.Stat.Concentration.iid_sum_chebyshev",
      "Causalean.Stat.IIDSample.map_tuple_eq",
      "Causalean.Stat.IIDSample.empProcVec_eq_stochEquicont_gap",
      "Causalean.Stat.empProcVec_chebyshev",
      "Causalean.Stat.empProcVec_sq_lintegral_le",
      "Causalean.Stat.hoeffding_decomp_order",
      "Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.rho_envelope_isLUB",
      "Causalean.Stat.secondMomentLM_inner",
      "Causalean.Stat.secondMomentLM_isPositive",
      "Causalean.Stat.stdGaussian_map_normSq_orthogonalProjection",
      "Causalean.Stat.Tendsto_dist.tightness",
      "Causalean.SteinMethod.steinSol_hasDerivAt",
      "ProbabilityTheory.condDistrib_map_of_condDistrib_fst_eq",
      "Causalean.Mathlib.CompProdAssembly.compProd_eq_of_inner_ae",
      "LinearMap.IsPositive.posSqrt_mul_self",
      "Causalean.ML.effectiveDimension_le_trace_div",
      "Causalean.Panel.EstimandCharacterization.HeterogeneousTWFE.DCDHPanel.twfe_eq_treated_weighted_tau_of_zeroUntreatedContrast",
      "Causalean.Panel.EstimandCharacterization.FlexibleDIDMundlak.VectorTWFEProblem.betaTWFE_normalEq",
    ];
    const entries = new Map(lib.entries.map((e) => [e.name, e]));
    expect(core.filter((name) => !entries.has(name))).toEqual([]);
    expect(core.filter((name) => !isTier1(entries.get(name)!, lib.sidecars))).toEqual([]);
  });
  it("drops a dangling review decl (drift) instead of throwing", () => {
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    try {
      const lib = loadLibrary(fixtureRoot({ badReviewDecl: true }));
      // Drift is tolerated: the stale review is filtered out, site still loads.
      expect(lib.sidecars.PO.reviews).toEqual([]);
      const foo = lib.entries.find((e) => e.name === "Causalean.PO.Foo")!;
      expect(reviewStatus(foo, lib.sidecars)).toBe("unreviewed");
      expect(warn).toHaveBeenCalledWith(expect.stringMatching(/unknown decl: Causalean\.PO\.Nope/));
    } finally {
      warn.mockRestore();
    }
  });
  it("throws on structural sidecar malformation (non-array field)", () => {
    expect(() => loadLibrary(fixtureRoot({ malformedSidecar: true }))).toThrow(/structural/);
  });
  it("linkifies known identifiers by longest match", () => {
    const lib = loadLibrary(fixtureRoot());
    const html = linkifyStatement("∀ n, Foo n = n + 1", lib, "/base");
    expect(html).toContain('href="/base/library/PO#Causalean.PO.Foo"');
    // the bare variable `n` must not be linked
    expect(html).not.toMatch(/<a[^>]*>n<\/a>/);
  });
  it("does not link a bare single-letter bound variable to a same-leaf field", () => {
    const lib = loadLibrary(fixtureRoot());
    const html = linkifyStatement("∀ W, 0 ≤ W", lib, "/base");
    // `W` collides with the field `Causalean.PO.System.W`; it must NOT link.
    expect(html).not.toMatch(/<a[^>]*>W<\/a>/);
    // …but the full name still resolves.
    const full = linkifyStatement("Causalean.PO.System.W", lib, "/base");
    expect(full).toContain('href="/base/library/PO#Causalean.PO.System.W"');
  });
  it("does not link a multi-name binder group member or its body recurrences", () => {
    const lib = loadLibrary(fixtureRoot());
    // `Foo` is a real decl, but here it is a BOUND variable: the first name in
    // the group `{Foo bar : Nat}` (so not immediately before the `:`) and reused
    // in the body. It must not link anywhere — mirrors the residualized regressor
    // `Dtilde` wrongly jumping to `GoodmanBacon.Dtilde`.
    const html = linkifyStatement("∀ {Foo bar : Nat}, bar = Foo", lib, "/base");
    expect(html).not.toMatch(/<a[^>]*>Foo<\/a>/);
    // a genuine reference (not bound here) still links.
    const ref = linkifyStatement("∀ n, Foo n = n", lib, "/base");
    expect(ref).toContain('href="/base/library/PO#Causalean.PO.Foo"');
  });
  it("sourceKind ignores a keyword-shaped word that only starts a docstring line", () => {
    // Regression: `id_sound_discrete`'s docstring reflows onto a line starting
    // "class. This is a *sound sufficient fragment*…" — sourceKind used to scan
    // raw `d.source` (docstring included) for the first line-initial keyword and
    // reported "class" for what is, on the declaration line itself, a theorem.
    const decl = {
      name: "Fixture.foo",
      kind: "theorem",
      module: "Fixture",
      file: "Fixture.lean",
      line: 1,
      statement: "",
      doc: null,
      refs: [],
      axioms: [],
      usesSorry: false,
      source: `/-- Identifies the query within the standard discrete positive model
class. This is a *sound sufficient fragment*, not the full algorithm. -/
theorem foo (x : Nat) : x = x := rfl`,
    };
    expect(sourceKind(decl)).toBe("theorem");
  });
});
