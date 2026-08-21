import { describe, it, expect } from "vitest";
import { placeSynthesizedDefinitions } from "../src/presentation/stages/p1_plan.js";
import { parseOutline } from "../src/presentation/stage_util.js";

// The outline `# Title` block is `**<Title>.** <one-line gloss/description>`.
// parseOutline must take ONLY the bold title — a regression caught in review where
// meta.json's title swallowed the trailing "We characterize…" description sentence.
describe("outline title extraction", () => {
  const outline = (titleLine: string) =>
    `# Title\n\n${titleLine}\n\n# Notation\n\n| a | b | c |\n\n# Sections\n`;

  it("takes only the bold title, dropping a trailing description sentence", () => {
    const t = parseOutline(
      outline(
        "**Minimax Offline Policy Learning under a Margin Condition.** We characterize the rate $n^{-r}$ proving the converse unconditionally.",
      ),
    ).title;
    expect(t).toBe("Minimax Offline Policy Learning under a Margin Condition");
  });

  it("handles a bold title with no trailing gloss", () => {
    expect(parseOutline(outline("**A Clean Title.**")).title).toBe("A Clean Title");
  });

  it("falls back to the whole line (sans emphasis/label/period) when not bolded", () => {
    expect(parseOutline(outline("Title: Some Plain Heading.")).title).toBe("Some Plain Heading");
  });

  it("treats none/(none)/n/a placeholders as an empty objs/bib list", () => {
    const md = [
      "# Title", "**T.**", "# Notation", "| a | b | c |", "# Sections",
      "## section: Introduction", "brief", "objs: (none)", "bib: none",
      "## section: Setup", "brief", "objs: P-1, P-2", "bib: smith2020",
    ].join("\n");
    const o = parseOutline(md);
    expect(o.sections[0].objs).toEqual([]); // "(none)" is not an obj id
    expect(o.sections[0].bib).toEqual([]); // "none" is not a bib key
    expect(o.sections[1].objs).toEqual(["P-1", "P-2"]);
  });
});

describe("synthesized-definition placement", () => {
  it("prepends synthetic env ids to the setup section exactly once", () => {
    const md = [
      "# Title", "**T.**", "# Notation", "| a | b | c |", "# Sections",
      "## section: Introduction", "brief", "objs: none", "bib: none",
      "## section: Setup and Assumptions", "brief", "objs: ass:x, def:y", "bib: smith2020",
    ].join("\n");
    const placed = placeSynthesizedDefinitions(md, ["synth_2", "synth_1", "synth_2"]);
    expect(parseOutline(placed).sections[1].objs).toEqual(["synth_2", "synth_1", "ass:x", "def:y"]);
  });
});

describe("parseOutline env_overrides", () => {
  const withOv = (line: string) => `# Title\n\n**T.** g\n\n${line}\n# Notation\n\n| a | b | c |\n\n# Sections\n`;
  it("honors all supported targets incl. colon-prefixed ids; drops + logs an unsupported one", () => {
    const errs: string[] = [];
    const orig = console.error;
    console.error = (m?: unknown) => { errs.push(String(m)); };
    try {
      const o = parseOutline(withOv("env_overrides: a1=definitionv, prop:x=propositionv, oeq:y=remarkv, def:est=algorithmv, b2=bogusv"));
      expect(o.envOverrides).toEqual({ a1: "definitionv", "prop:x": "propositionv", "oeq:y": "remarkv", "def:est": "algorithmv" });
      expect(errs.some((m) => /b2=bogusv ignored/.test(m))).toBe(true); // not silently dropped
    } finally {
      console.error = orig;
    }
  });
});

describe("appendix heading decoration", () => {
  it("strips a doubled letter, an Appendix word, and both together", async () => {
    const { stripAppendixHeadingDecoration: f } = await import("../src/presentation/stages/p2_draft.js");
    // The stripped enumerator carried the capital, so the title is re-capitalized.
    expect(f("\\section{B: empirical process lemmas")).toBe("\\section{Empirical process lemmas");
    expect(f("\\section{A. proofs")).toBe("\\section{Proofs");
    expect(f("\\section{Appendix: verification note")).toBe("\\section{Verification note");
    expect(f("\\section{Appendix B: proofs")).toBe("\\section{Proofs");
    // An untouched title keeps its case, and a title opening with math/macro is left alone.
    expect(f("\\section{proofs of the main results")).toBe("\\section{proofs of the main results");
    expect(f("\\section{B: \\(\\theta\\) bounds")).toBe("\\section{\\(\\theta\\) bounds");
    expect(f("\\section{A note on fixed codes")).toBe("\\section{A note on fixed codes");
  });
});

describe("main-body placement of statement dependencies", () => {
  it("flags a definition stranded in an appendix and accepts proof-only appendix lemmas", async () => {
    const { lintMainBodyDependencies, parseOutline } = await import("../src/presentation/stage_util.js");
    const md = [
      "# Title", "T", "# Notation", "", "# Sections",
      "## section: Main results", "objs: thm:main",
      "## section: Appendix A: proofs", "objs: def:estimator, lem:helper",
    ].join("\n");
    const outline = parseOutline(md);
    const kinds: Record<string, string> = { "thm:main": "theorem", "def:estimator": "definition", "lem:helper": "lemma" };
    const problems = lintMainBodyDependencies(outline, (id) => (id === "thm:main" ? ["def:estimator"] : []), (id) => kinds[id]);
    expect(problems).toHaveLength(1);
    expect(problems[0]).toContain("def:estimator");
    expect(problems[0]).toContain("Main results");
    // A proof-only dependency (no statement-uses edge) is not flagged.
    expect(lintMainBodyDependencies(outline, () => [], (id) => kinds[id])).toEqual([]);
  });
});

describe("algorithmv body lock", () => {
  it("releases an unstepped frozen body but keeps a validated stepped one", async () => {
    const { isSteppedBodyForTest } = await import("../src/presentation/stages/p1_plan.js");
    expect(isSteppedBodyForTest("Let x be the statistic. Then it converges.")).toBe(false);
    expect(isSteppedBodyForTest("\\begin{enumerate}\\item Split the sample.\\end{enumerate}")).toBe(true);
    expect(isSteppedBodyForTest("Inputs are named. \\item Output the statistic.")).toBe(true);
  });
});
