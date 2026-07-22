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
      const o = parseOutline(withOv("env_overrides: a1=definitionv, prop:x=propositionv, oeq:y=remarkv, b2=bogusv"));
      expect(o.envOverrides).toEqual({ a1: "definitionv", "prop:x": "propositionv", "oeq:y": "remarkv" });
      expect(errs.some((m) => /b2=bogusv ignored/.test(m))).toBe(true); // not silently dropped
    } finally {
      console.error = orig;
    }
  });
});
