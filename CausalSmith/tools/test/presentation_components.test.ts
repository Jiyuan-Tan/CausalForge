import { describe, it, expect } from "vitest";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { componentSignature, buildDeclList, ensureComponentsForEnvs, type ComponentSpec, type ModuleDecl } from "../src/presentation/components.js";
import type { CrosswalkEntry } from "../src/types.js";

describe("componentSignature (cache/drift key for a component set)", () => {
  it("is order-independent across specs and binders", () => {
    const a: ComponentSpec[] = [
      { type: "decl", decl: "LindebergScale" },
      { type: "hypotheses", theorem: "t1_thm", binders: ["_h_L2_oracle", "_h_L2_plug"] },
    ];
    const b: ComponentSpec[] = [
      { type: "hypotheses", theorem: "t1_thm", binders: ["_h_L2_plug", "_h_L2_oracle"] },
      { type: "decl", decl: "LindebergScale" },
    ];
    expect(componentSignature(a)).toBe(componentSignature(b));
  });

  it("distinguishes a different decl set", () => {
    expect(componentSignature([{ type: "decl", decl: "ProportionalFolds" }])).not.toBe(
      componentSignature([{ type: "decl", decl: "LindebergScale" }]),
    );
  });
});

describe("buildDeclList (discovery prompt pool)", () => {
  const cw = (obj_id: string, decl: string | null, file = "Basic.lean"): CrosswalkEntry => ({
    obj_id,
    kind: "definition",
    title: obj_id,
    tex: { label: `obj:${obj_id}`, line_range: "1" },
    lean: decl == null ? null : { file, decl, decl_kind: "def", line: 1 },
    verdict: "exact",
  });

  it("includes crosswalk decls + def/abbrev/structure module decls, dedups, drops non-def kinds", () => {
    const crosswalk = [cw("P-8", "LindebergScale"), cw("P-7", null)];
    const mods = new Map<string, ModuleDecl>([
      ["LindebergScale", { file: "Basic.lean", line: 635, kind: "def" }], // dup of crosswalk decl
      ["ProportionalFolds", { file: "Basic.lean", line: 615, kind: "def" }],
      ["t1_thm", { file: "T1.lean", line: 10, kind: "theorem" }], // not a def → excluded
    ]);
    const list = buildDeclList(crosswalk, mods).split("\n");
    expect(list).toContain("LindebergScale : Basic.lean");
    expect(list).toContain("ProportionalFolds : Basic.lean");
    expect(list.some((l) => l.startsWith("t1_thm"))).toBe(false); // theorem excluded from the def pool
    expect(list.filter((l) => l.startsWith("LindebergScale")).length).toBe(1); // deduped
  });
});

describe("ensureComponentsForEnvs cache validation", () => {
  it("recomputes a same-key cache entry that fails ComponentSpecSchema", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "components-cache-"));
    try {
      const cachePath = path.join(dir, "components_cache.json");
      await writeFile(cachePath, JSON.stringify({ "A-1": { key: "bad", components: [{ type: "hypotheses", theorem: "t", binders: "H1" }] } }), "utf8");
      const env = { env: "assumptionv" as const, obj_id: "A-1", title: null, body: "body", order: 0 };
      const key = (await import("../src/presentation/tex_anchors.js")).hashEnvBody("body");
      await writeFile(cachePath, JSON.stringify({ "A-1": { key, components: [{ type: "hypotheses", theorem: "t", binders: "H1" }] } }), "utf8");
      let calls = 0;
      const res = await ensureComponentsForEnvs({
        envs: [env],
        crosswalk: [{ obj_id: "A-1", kind: "assumption", title: "A", tex: { label: "A-1", line_range: "" }, lean: null, verdict: "unmatched" }],
        repoRoot: dir,
        leanSubdir: "Lean",
        cachePath,
        deps: {
          runCodex: async () => {
            calls++;
            return { stdout: JSON.stringify({ components: [{ type: "hypotheses", theorem: "t", binders: ["H1"] }] }), stderr: "" };
          },
        },
      });
      expect(calls).toBe(1);
      expect(res.components["A-1"]).toEqual([{ type: "hypotheses", theorem: "t", binders: ["H1"] }]);
      expect(await readFile(cachePath, "utf8")).toContain('"binders": [');
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});
