import { describe, it, expect } from "vitest";
import { replaceEnvBody, normalizeFrozenEnvs, parseAnchoredEnvs } from "../src/presentation/tex_anchors.js";

const TEX = `intro
\\begin{theoremv}{T-1}[Rate]
the rate is n^{-1/2}.
\\end{theoremv}
between
\\begin{definitionv}{P-2}
old def body.
\\end{definitionv}
end`;

describe("replaceEnvBody", () => {
  it("replaces only the targeted env body, preserving kind/obj-id/title", () => {
    const out = replaceEnvBody(TEX, "T-1", "the rate is n^{-1/2}, for measurable f.");
    const envs = parseAnchoredEnvs(out);
    const t1 = envs.find((e) => e.obj_id === "T-1")!;
    expect(t1.env).toBe("theoremv");
    expect(t1.title).toBe("Rate");
    expect(t1.body.trim()).toBe("the rate is n^{-1/2}, for measurable f.");
    // the other env is untouched
    expect(envs.find((e) => e.obj_id === "P-2")!.body.trim()).toBe("old def body.");
  });

  it("returns the tex unchanged when the obj-id is not present", () => {
    expect(replaceEnvBody(TEX, "Z-9", "x")).toBe(TEX);
  });

  it("re-imposes canonical frozen blocks after a prose reviser paraphrases one", () => {
    const canonical = new Map([["T-1", `\\begin{theoremv}{T-1}[Rate]\nthe rate is n^{-1/2}.\n\\end{theoremv}`]]);
    const drifted = TEX.replace("the rate is n^{-1/2}.", "the rate is faster than n^{-1/2}.");
    const normalized = normalizeFrozenEnvs(drifted, canonical);
    expect(parseAnchoredEnvs(normalized).find((e) => e.obj_id === "T-1")?.body.trim()).toBe("the rate is n^{-1/2}.");
    expect(normalized).toContain("old def body.");
  });
});
