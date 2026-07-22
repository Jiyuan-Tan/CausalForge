import { describe, it, expect } from "vitest";
import { mkdtemp, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { buildBundle, paperLabels, assumptionTable } from "../src/presentation/emit.js";
import { tex2html } from "../src/presentation/tex2html.js";
import { parseAnchoredEnvs, type AnchoredEnv } from "../src/presentation/tex_anchors.js";
import { parseNoteBlocks, type NoteBlock } from "../src/presentation/note_parser.js";
import { parseBib } from "../src/presentation/citations.js";
import type { CrosswalkEntry } from "../src/presentation/types.js";

const PAPER = `
\\begin{assumptionv}{P-2}[Overlap tail]
Tail body.
\\end{assumptionv}
\\begin{definitionv}{P-1}[Setup]
Setup body.
\\end{definitionv}
\\begin{theoremv}{T-1}[Upper bound]
Risk bound body.
\\end{theoremv}
`;

const NOTE = `## 6. T-block

### T-1. Upper bound.

#### Load-bearing hypotheses.
- **H1 (A1 Identification).** P-1 with consistency.
- **H2 (A2 Overlap tail).** P-2 with decay.

#### Conclusion.
- Bound.
`;

const cwRow = (obj_id: string, kind: string, lean: CrosswalkEntry["lean"]): CrosswalkEntry => ({
  obj_id, kind, title: "", tex: null, lean, verdict: "",
});

describe("bundle join", () => {
  it("numbers per env class and joins lean snippets + fallbacks", async () => {
    const dir = await mkdtemp(join(tmpdir(), "psmith-emit-"));
    await writeFile(
      join(dir, "T1.lean"),
      "theorem t1_thm (H1 : Nat) (H2 : Nat) :\n    1 ≤ 2 := by\n  omega\n",
      "utf8",
    );
    const envs = parseAnchoredEnvs(PAPER);
    const labels = paperLabels(envs);
    expect(labels.get("P-2")).toBe("Assumption 1");
    expect(labels.get("P-1")).toBe("Definition 1");
    expect(labels.get("T-1")).toBe("Theorem 1");

    const bundle = await buildBundle({
      envs,
      crosswalk: [
        cwRow("P-2", "assumption", null),
        cwRow("P-1", "definition", null),
        cwRow("T-1", "theorem", { file: "T1.lean", decl: "t1_thm", decl_kind: "theorem", line: 1 }),
      ],
      blocks: parseNoteBlocks(NOTE),
      repoRoot: dir,
      leanSubdir: ".",
      commit: "abc123",
      verdictByObj: new Map([["T-1", { status: "matched" }]]),
    });
    expect(bundle.crosswalk.commit).toBe("abc123");
    expect(bundle.crosswalk.entries).toHaveLength(3);
    const t1 = bundle.crosswalk.entries.find((e) => e.obj_id === "T-1")!;
    expect(t1.paper_label).toBe("Theorem 1");
    expect(bundle.snippets.snippets["T-1"].statement).toContain("theorem t1_thm");
    expect(bundle.snippets.snippets["T-1"].statement).not.toContain("omega");
    expect(bundle.snippets.snippets["T-1"].sorry_free).toBe(true);
    // honesty fields: verified status carried verbatim; sorry-free mirrors the snippet
    expect(t1.status).toBe("matched");
    expect(t1.sorry_free).toBe(true);
    const p2 = bundle.crosswalk.entries.find((e) => e.obj_id === "P-2")!;
    expect(p2.lean).toBeNull();
    expect(p2.fallback).toBeTruthy();
    expect(p2.status).toBe("unreviewed"); // not in verdictByObj → default
    expect(p2.sorry_free).toBeNull(); // no snippet (fallback object)
    await rm(dir, { recursive: true, force: true });
  });

  it("renders a multi-part definition as a composite (all pieces), nulling the single lean ref", async () => {
    const dir = await mkdtemp(join(tmpdir(), "psmith-comp-"));
    await writeFile(
      join(dir, "Basic.lean"),
      [
        "/-- beta -/",
        "noncomputable def betaWeak (a g : ℝ) : ℝ := if g = 0 then 0 else a",
        "/-- D -/",
        "noncomputable def Dweak (a g : ℝ) : ℝ := 2 + a",
        "/-- r -/",
        "noncomputable def rStar (a g : ℝ) : ℝ := (1 + a) / Dweak a g",
      ].join("\n") + "\n",
      "utf8",
    );
    const envs = parseAnchoredEnvs(`\\begin{definitionv}{P-2}[Exponents]\nbody\n\\end{definitionv}`);
    const bundle = await buildBundle({
      envs,
      // crosswalk maps P-2 to a SINGLE decl (betaWeak); Dweak/rStar are not entries
      crosswalk: [cwRow("P-2", "definition", { file: "Basic.lean", decl: "betaWeak", decl_kind: "def", line: 2 })],
      blocks: [],
      repoRoot: dir,
      leanSubdir: ".",
      commit: "c",
      components: {
        "P-2": [
          { type: "decl", decl: "betaWeak" },
          { type: "decl", decl: "Dweak" },
          { type: "decl", decl: "rStar" },
        ],
      },
      // Dweak/rStar resolvable only via the module index, not the crosswalk
      moduleDecls: new Map([
        ["Dweak", { file: "Basic.lean", line: 4 }],
        ["rStar", { file: "Basic.lean", line: 6 }],
      ]),
    });
    const snip = bundle.snippets.snippets["P-2"];
    expect(snip.decl).toBe("(composite)");
    expect(snip.components?.map((c) => c.label)).toEqual(["betaWeak", "Dweak", "rStar"]);
    expect(snip.components?.[1].statement).toContain("def Dweak");
    const entry = bundle.crosswalk.entries.find((e) => e.obj_id === "P-2")!;
    expect(entry.lean).toBeNull(); // composite ⇒ no single representative decl
    expect(entry.fallback).toBeTruthy();
    await rm(dir, { recursive: true, force: true });
  });

  it("keeps the single-decl view when only one piece is mapped", async () => {
    const dir = await mkdtemp(join(tmpdir(), "psmith-single-"));
    await writeFile(join(dir, "Basic.lean"), "/-- m -/\nnoncomputable def mu (x : ℝ) : ℝ := x\n", "utf8");
    const envs = parseAnchoredEnvs(`\\begin{definitionv}{P-6}[Nuisance]\nbody\n\\end{definitionv}`);
    const bundle = await buildBundle({
      envs,
      crosswalk: [cwRow("P-6", "definition", { file: "Basic.lean", decl: "mu", decl_kind: "def", line: 2 })],
      blocks: [],
      repoRoot: dir,
      leanSubdir: ".",
      commit: "c",
      components: { "P-6": [{ type: "decl", decl: "mu" }] },
    });
    const snip = bundle.snippets.snippets["P-6"];
    expect(snip.decl).toBe("mu");
    expect(snip.components).toBeUndefined();
    expect(bundle.crosswalk.entries.find((e) => e.obj_id === "P-6")!.lean).not.toBeNull();
    await rm(dir, { recursive: true, force: true });
  });

  it("fails on an env missing from the crosswalk", async () => {
    await expect(
      buildBundle({
        envs: parseAnchoredEnvs(PAPER),
        crosswalk: [cwRow("P-2", "assumption", null)],
        blocks: [],
        repoRoot: "/nowhere",
        leanSubdir: ".",
        commit: "c",
      }),
    ).rejects.toThrow(/not in bank crosswalk/);
  });

  it("emits presentation-synthesized definitions without a bank crosswalk row", async () => {
    const envs = parseAnchoredEnvs("\\begin{definitionv}{synth_1}[Notation] body \\end{definitionv}");
    const bundle = await buildBundle({
      envs,
      crosswalk: [],
      blocks: [],
      repoRoot: "/nowhere",
      leanSubdir: ".",
      commit: "c",
      verdictByObj: new Map([["synth_1", { status: "presentation-synthesized" }]]),
    });
    expect(bundle.crosswalk.entries[0]).toMatchObject({
      obj_id: "synth_1", lean: null, status: "presentation-synthesized",
    });
  });
});

describe("assumption table", () => {
  const blocks = parseNoteBlocks(NOTE);
  const envs = parseAnchoredEnvs(PAPER);

  it("is total when hypotheses and refs are all presented", () => {
    const { md, problems } = assumptionTable(blocks, envs, {
      "T-1": { decl: "t1_thm", file: "T1.lean", line: 1, statement: "theorem t1_thm (H1 : A) (H2 : B) : C", sorry_free: true, axioms: null },
    });
    expect(problems).toEqual([]);
    // assumptionTable renders a markdown table mapping each Lean hypothesis to
    // its source object(s): `| Theorem | Hypothesis | Source objects | Status |`.
    // H1 references P-1 (Definition 1), H2 references P-2 (Assumption 1).
    expect(md).toContain("| H1 | Definition 1 (P-1) | presented |");
    expect(md).toContain("| H2 | Assumption 1 (P-2) | presented |");
  });

  it("flags a Lean hypothesis missing from the note and an unpresented ref", () => {
    const { problems } = assumptionTable(blocks, envs, {
      "T-1": { decl: "t1_thm", file: "T1.lean", line: 1, statement: "theorem t1_thm (H1 : A) (H9 : Z) : C", sorry_free: true, axioms: null },
    });
    expect(problems.some((p) => p.includes("H9"))).toBe(true);
    const fewerEnvs = parseAnchoredEnvs(PAPER.replace(/\\begin\{assumptionv\}[\s\S]*?\\end\{assumptionv\}/, ""));
    const { problems: p2 } = assumptionTable(blocks, fewerEnvs, {
      "T-1": { decl: "t1_thm", file: "T1.lean", line: 1, statement: "theorem t1_thm (H1 : A) : C", sorry_free: true, axioms: null },
    });
    expect(p2.some((p) => p.includes("P-2"))).toBe(true);
  });

  it("scans component statements for a composite theorem (empty top-level statement)", () => {
    // A composite theorem carries `statement: ""`; before the fix the totality
    // check scanned the empty string → ZERO binders → silently exempted the
    // theorem. Now it scans the component statements, so a hypothesis missing
    // from the note (H9) is still caught.
    const { problems } = assumptionTable(blocks, envs, {
      "T-1": {
        decl: "(composite)",
        file: "T1.lean",
        line: 1,
        statement: "",
        sorry_free: true,
        axioms: null,
        components: [{ label: "t1_thm", statement: "theorem t1_thm (H1 : A) (H9 : Z) : C" }],
      },
    });
    expect(problems.some((p) => p.includes("H9"))).toBe(true);
  });

  it("falls back to inline ass: refs (note or paper env body) when there is no Load-bearing field", () => {
    // Shared-assumption-lattice notes carry no per-theorem `Load-bearing hypotheses` field; the
    // standing assumption is referenced inline — bare `ass:foo` in the note, or `\ref{obj:ass:bar}`
    // in the frozen paper env (a headline lower-bound theorem whose symbolic note Statement has no
    // ref). Both must satisfy totality without an H1/H2 field or a Lean-snippet binder.
    const altBlocks: NoteBlock[] = [
      { obj_id: "thm:a", title: "", body: "Under ass:foo the identity holds.", fields: { statement: "Under ass:foo the identity holds." } },
      { obj_id: "thm:b", title: "", body: "M_n >= c, symbolic only.", fields: { statement: "M_n >= c, symbolic only." } },
    ];
    const altEnvs: AnchoredEnv[] = [
      { env: "theoremv", obj_id: "thm:a", title: null, body: "Under ass:foo the identity holds.", order: 1 },
      { env: "theoremv", obj_id: "thm:b", title: null, body: "Under Assumption~\\ref{obj:ass:bar}, M_n \\ge c.", order: 2 },
      { env: "assumptionv", obj_id: "ass:foo", title: null, body: "foo.", order: 3 },
      { env: "assumptionv", obj_id: "ass:bar", title: null, body: "bar.", order: 4 },
    ];
    const { problems } = assumptionTable(altBlocks, altEnvs, {});
    expect(problems).toEqual([]); // thm:a via note `ass:foo`; thm:b via env-body `\ref{obj:ass:bar}`

    // …but a theorem with NO ass: ref anywhere (and no H1/H2 field) still fails totality.
    const { problems: p2 } = assumptionTable(
      [{ obj_id: "thm:a", title: "", body: "No hypotheses anywhere.", fields: {} }],
      [{ env: "theoremv", obj_id: "thm:a", title: null, body: "No hypotheses anywhere.", order: 1 }],
      {},
    );
    expect(p2.some((p) => p.includes("no load-bearing hypotheses"))).toBe(true);
  });

  it("does not resurrect an explicitly dropped hypothesis from a drift-watch field", () => {
    const droppedBlocks: NoteBlock[] = [{
      obj_id: "thm:headline",
      title: "",
      body: "**Statement.** Under ass:live, the bound holds.\n\n**Hypothesis dropped from this theorem (drift-watch).** ass:obsolete is not load-bearing.",
      fields: {
        Statement: "Under ass:live, the bound holds.",
        "Hypothesis dropped from this theorem (drift-watch)": "ass:obsolete is not load-bearing.",
      },
    }];
    const droppedEnvs: AnchoredEnv[] = [
      { env: "theoremv", obj_id: "thm:headline", title: null, body: "Under ass:live, the bound holds.", order: 1 },
      { env: "assumptionv", obj_id: "ass:live", title: null, body: "Live assumption.", order: 2 },
    ];
    const { problems, md } = assumptionTable(droppedBlocks, droppedEnvs, {});
    expect(problems).toEqual([]);
    expect(md).toContain("ass:live");
    expect(md).not.toContain("ass:obsolete");
  });

  it("accepts a current Lean theorem with parameters but no H-binders as hypothesis-free", () => {
    const { problems, md } = assumptionTable(
      [{ obj_id: "thm:headline", title: "", body: "For every m >= 3.", fields: {} }],
      [{ env: "theoremv", obj_id: "thm:headline", title: null, body: "For every \\(m\\ge3\\).", order: 1 }],
      {
        "thm:headline": {
          decl: "headline",
          file: "Headline.lean",
          line: 1,
          statement: "theorem headline (m : ℕ) (hm : 3 ≤ m) : P m",
          sorry_free: true,
          axioms: null,
        },
      },
    );
    expect(problems).toEqual([]);
    expect(md).toContain("| — | — | presented |");
  });
});

describe("tex2html (requires pandoc)", () => {
  // pandoc spawns are fast in plain node (~70ms) but can take ~10s each under
  // vitest worker threads on the cluster; budget accordingly.
  it("wraps anchored envs in data-objid divs and renders cites", { timeout: 120_000 }, async () => {
    const tex = `\\documentclass{article}\\begin{document}
\\begin{abstract}We bound things \\citep{robins1994}.\\end{abstract}
\\section{Introduction}
Opening context.
\\section{Results}\\label{sec:results}
Prose with math \\(x^2\\) and \\citet{robins1994}. See \\cref{obj:P-1,obj:T-1} in \\cref{sec:results}.
${PAPER}
\\begin{proof}[Proof of Theorem 1]
Trivial and 100\\% exact.
\\[
x=1.
\\] % lean: t1_thm
\\end{proof}
\\end{document}`;
    const bib = parseBib(
      `@article{robins1994, title = {Estimation}, author = {Robins, James M. and Rotnitzky, Andrea}, year = {1994}, doi = {10/x}\n}`,
    );
    const html = await tex2html(tex, bib);
    expect(html).toContain('data-objid="T-1"');
    expect(html).toContain('data-objid="P-2"');
    expect(html).toContain("Theorem 1");
    expect(html).toContain("Robins et al. (1994)");
    expect(html).toContain("(Robins et al., 1994)");
    expect(html).toContain('class="abstract"');
    expect(html).toContain('class="proof"');
    expect(html).toContain("100%");
    expect(html).not.toContain("% lean:");
    expect(html).toContain("References");
    expect(html).not.toContain("PSMITHBLOCK");
    expect(html).not.toContain("\\begin{theoremv}");
    expect(html).toContain('definition <a class="objref" href="#obj-P-1">1</a>');
    expect(html).toContain('theorem <a class="objref" href="#obj-T-1">1</a>');
    expect(html).toContain("section 2");
    expect(html).not.toContain("\\cref");
  });

  it("keeps bracketed math titles intact in formal blocks", { timeout: 120_000 }, async () => {
    const tex = `\\documentclass{article}\\begin{document}
\\begin{definitionv}{def:law-class}[Class \\(\\mathcal{P}_{[0,1]}\\)]
Members are supported on \\([0,1]\\).
\\end{definitionv}
\\end{document}`;
    const html = await tex2html(tex, []);
    expect(html).toContain('data-objid="def:law-class"');
    expect(html).toContain("Class");
    expect(html).toContain("\\mathcal{P}_{[0,1]}");
    expect(html).toContain("Members are supported");
    expect(html).not.toContain("}\\)]");
  });

  it("preserves generated cited-dependency scope footnotes on the web", { timeout: 120_000 }, async () => {
    const tex = `\\documentclass{article}\\begin{document}
\\begin{theoremv}{thm:main}[Main]*
The bound holds.
\\end{theoremv}
\\verificationfootnotetext{\\textbf{Formalization scope.} This uses \\citep{smith2025}; the source proof is not formalized here.}
\\end{document}`;
    const bib = parseBib(
      `@article{smith2025, title = {A bound}, author = {Smith, Jane}, year = {2025}}`,
    );
    const html = await tex2html(tex, bib);
    expect(html).toContain('class="verification-footnote"');
    expect(html).toContain("Formalization scope");
    expect(html).toContain("(Smith, 2025)");
    expect(html).not.toContain("verificationfootnote");
    expect(html).not.toContain("<p>* The bound holds");
  });

  it("keeps presentation-only formal blocks inert when they have no Lean target", { timeout: 120_000 }, async () => {
    const tex = `\\documentclass{article}\\begin{document}
\\begin{definitionv}{synth_1}[Notation]
Presentation-only notation.
\\end{definitionv}
\\begin{theoremv}{thm:main}[Main]
Lean-backed result.
\\end{theoremv}
\\end{document}`;
    const html = await tex2html(tex, [], new Set(["thm:main"]));
    expect(html).toContain('id="obj-synth_1" data-presentation-only="true"');
    expect(html).not.toContain('data-objid="synth_1"');
    expect(html).toContain('data-objid="thm:main" tabindex="0"');
  });
});

import { buildSymbolRealizations, symbolProseTargets } from "../src/presentation/emit.js";
import { discoverRealizedSymbols, buildSymbolClusters } from "../src/formalization/crosswalk.js";

const SYM_LEAN = `namespace Demo
/-- carrier
@realizes mu_0(carrier 𝒳→ℝ; range via Bdd), mu_1(carrier 𝒳→ℝ) -/
structure Law where
  mu0 : ℝ
  mu1 : ℝ

-- @node: bdd
/-- range predicate -/
def Bdd (P : Law) : Prop :=
  P.mu0 ≥ -1 -- @realizes mu_0(mu0 ≥ -1)
end Demo
`;

describe("buildSymbolRealizations (@realizes → web)", () => {
  it("discovers every tagged symbol, builds one composite per symbol, dedups by decl, drops @node", async () => {
    const dir = await mkdtemp(join(tmpdir(), "symrz-"));
    try {
      await writeFile(join(dir, "Demo.lean"), SYM_LEAN, "utf8");
      const syms = await discoverRealizedSymbols(dir);
      expect(new Set(syms)).toEqual(new Set(["mu_0", "mu_1"])); // both tags discovered

      const clusters = await buildSymbolClusters(dir, syms.map((name) => ({ name })));
      const { entries, snippets, items } = await buildSymbolRealizations({
        clusters,
        repoRoot: dir,
        leanSubdir: ".",
      });

      // arm pair mu_0/mu_1 synthesizes a generic mu_a (merged) so the paper's `μ_a(x)` is clickable
      expect(entries.find((e) => e.obj_id === "sym:mu_a")).toBeDefined();
      expect(snippets["sym:mu_a"].components!.length).toBe(2); // Law + Bdd, deduped across both arms
      // the panel still lists the actual tags for completeness
      expect(items.map((i) => i.obj_id)).toContain("sym:mu_0");

      // symbolProseTargets (what P2 \leanref-links) prefers the GENERIC mu_a over its arms
      const targets = symbolProseTargets(clusters);
      expect(targets.map((t) => t.name)).toContain("mu_a");
      expect(targets.map((t) => t.name)).not.toContain("mu_0");
      expect(targets.map((t) => t.name)).not.toContain("mu_1");
      expect(targets.find((t) => t.name === "mu_a")!.objId).toBe("sym:mu_a");
      expect(targets.find((t) => t.name === "mu_a")!.description).toBeTruthy();

      const mu0 = entries.find((e) => e.obj_id === "sym:mu_0")!;
      expect(mu0.env).toBe("symbol");
      expect(mu0.lean).toBeNull(); // composite — no single representative decl
      expect(mu0.paper_label).toBe("mu_0");

      const snip = snippets["sym:mu_0"];
      // mu_0 is realized by TWO decls (Law structure + Bdd); deduped → 2 components, not 3 tags
      expect(snip.components!.length).toBe(2);
      expect(snip.components!.map((c) => c.label.split(" ")[0]).sort()).toEqual(["Bdd", "Law"]);
      // the realizing Lean code is shown, with NO @node bleed
      expect(snip.components!.some((c) => c.statement.includes("structure Law"))).toBe(true);
      expect(JSON.stringify(snip.components)).not.toContain("@node");

      // formal-layer item for the panel
      expect(items.find((i) => i.obj_id === "sym:mu_0")!.kind).toBe("symbol");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});

describe("stale Lean paths are reported honestly", () => {
  // Regression: a banked node's `lean.file` goes stale when the Lean tree is refactored
  // after banking (measured: 8/29 refs in eid_lingam, 4/17 in panel_ppml). The reader used
  // to swallow the read error and return "", making a RENAMED file indistinguishable from
  // a decl that genuinely has no standalone statement — which published a false
  // "No standalone Lean declaration." for 18 nodes that DO carry a decl_name.
  it("does not claim 'no standalone Lean declaration' when the source file is merely missing", async () => {
    const dir = await mkdtemp(join(tmpdir(), "psmith-stale-"));
    try {
      const envs = parseAnchoredEnvs(
        `\\begin{theoremv}{T-1}[Upper bound]\nRisk bound body.\n\\end{theoremv}`,
      );
      const bundle = await buildBundle({
        envs,
        crosswalk: [
          // Points at a file that does not exist on disk — the stale-path case.
          cwRow("T-1", "theorem", {
            file: "Helpers/Removed.lean",
            decl: "t1_thm",
            decl_kind: "theorem",
            line: 1,
          }),
        ],
        blocks: [],
        repoRoot: dir,
        leanSubdir: ".",
        commit: "abc123",
      });
      const t1 = bundle.crosswalk.entries.find((e) => e.obj_id === "T-1")!;
      expect(t1.fallback).toBeTruthy();
      // The reader must be told the path is stale, NOT that the object is unformalized
      // or that it was deliberately re-exported from elsewhere.
      expect(t1.fallback).toContain("Helpers/Removed.lean");
      expect(t1.fallback!.toLowerCase()).toContain("stale");
      expect(t1.fallback).not.toContain("No standalone Lean declaration");
      expect(t1.fallback).not.toContain("re-exported");
      // And a file we could not read must never cast a sorry-free vote.
      expect(t1.sorry_free).not.toBe(true);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});
