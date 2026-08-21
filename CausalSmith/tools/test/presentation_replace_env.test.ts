import { describe, it, expect } from "vitest";
import { normalizeFrozenEnvs, parseAnchoredEnvs } from "../src/presentation/tex_anchors.js";

const TEX = `intro
\\begin{theoremv}{T-1}[Rate]
the rate is n^{-1/2}.
\\end{theoremv}
between
\\begin{definitionv}{P-2}
old def body.
\\end{definitionv}
end`;

describe("normalizeFrozenEnvs", () => {
  it("re-imposes canonical frozen blocks after a prose reviser paraphrases one", () => {
    const canonical = new Map([["T-1", `\\begin{theoremv}{T-1}[Rate]\nthe rate is n^{-1/2}.\n\\end{theoremv}`]]);
    const drifted = TEX.replace("the rate is n^{-1/2}.", "the rate is faster than n^{-1/2}.");
    const normalized = normalizeFrozenEnvs(drifted, canonical);
    expect(parseAnchoredEnvs(normalized).find((e) => e.obj_id === "T-1")?.body.trim()).toBe("the rate is n^{-1/2}.");
    expect(normalized).toContain("old def body.");
  });
});
