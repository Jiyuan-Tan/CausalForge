import { describe, it, expect } from "vitest";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { assembleComponentText, componentSignature, buildDeclList, ensureComponentsForEnvs, type ComponentSpec, type ModuleDecl } from "../src/presentation/components.js";
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

  it("does not trust a stale content-only empty-cache entry", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "components-cache-empty-"));
    try {
      const cachePath = path.join(dir, "components_cache.json");
      await writeFile(cachePath, JSON.stringify({ "A-1": { key: "legacy-body-key", components: [] } }), "utf8");
      let calls = 0;
      const res = await ensureComponentsForEnvs({
        envs: [{ env: "assumptionv", obj_id: "A-1", title: null, body: "body", order: 0 }],
        crosswalk: [{ obj_id: "A-1", kind: "assumption", title: "A", tex: null, lean: null, verdict: "unmatched" }],
        repoRoot: dir, leanSubdir: "Lean", cachePath,
        deps: { runCodex: async () => {
          calls++;
          return { stdout: JSON.stringify({ components: [{ type: "decl", decl: "Fresh" }] }), stderr: "" };
        } },
      });
      expect(calls).toBe(1);
      expect(res.components["A-1"]).toEqual([{ type: "decl", decl: "Fresh" }]);
      expect(res.complete["A-1"]).toBe(true);
      expect(JSON.parse(await readFile(cachePath, "utf8"))["A-1"]).toMatchObject({
        policy: "component-discovery-v2", complete: true,
      });
    } finally { await rm(dir, { recursive: true, force: true }); }
  });

  it("does not trust a cache entry without an explicit completeness receipt", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "components-cache-incomplete-"));
    try {
      const cachePath = path.join(dir, "components_cache.json");
      await writeFile(cachePath, JSON.stringify({ "A-1": {
        policy: "component-discovery-v2", key: "forged", complete: false,
        components: [{ type: "decl", decl: "OnlyOneOfSeveral" }],
      } }), "utf8");
      let calls = 0;
      await ensureComponentsForEnvs({
        envs: [{ env: "assumptionv", obj_id: "A-1", title: null, body: "body", order: 0 }],
        crosswalk: [{ obj_id: "A-1", kind: "assumption", title: "A", tex: null, lean: null, verdict: "unmatched" }],
        repoRoot: dir, leanSubdir: "Lean", cachePath,
        deps: { runCodex: async () => {
          calls++;
          return { stdout: JSON.stringify({ components: [] }), stderr: "" };
        } },
      });
      expect(calls).toBe(1);
    } finally { await rm(dir, { recursive: true, force: true }); }
  });

  it("invalidates v2 receipts when inventory, source statements, crosswalk, or graph provenance changes", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "components-cache-universe-"));
    try {
      await mkdir(path.join(dir, "Lean"));
      const candidatePath = path.join(dir, "Lean", "Candidate.lean");
      const theoremPath = path.join(dir, "Lean", "Theorem.lean");
      await writeFile(candidatePath, "def CandidateA : Nat := 1\n", "utf8");
      await writeFile(theoremPath, "theorem SourceThm : True := trivial\n", "utf8");
      const cachePath = path.join(dir, "components_cache.json");
      const envs = [{ env: "assumptionv" as const, obj_id: "A-1", title: null, body: "body", order: 0 }];
      const baseCrosswalk: CrosswalkEntry[] = [
        { obj_id: "A-1", kind: "assumption", title: "A", tex: { label: "A-1", line_range: "" }, lean: null, verdict: "unmatched" },
        { obj_id: "T-1", kind: "theorem", title: "T", tex: { label: "T-1", line_range: "" },
          lean: { file: "Theorem.lean", decl: "SourceThm", decl_kind: "theorem", line: 1 }, verdict: "exact" },
      ];
      const baseGraph = { qid: "q", specialization: "s", nodes: [{
        id: "A-1", kind: "assumption", provenance: "from-note",
        nl: { statement: "A", tex_anchor: "A-1", frozen: true },
        lean: { decl_name: null, file: null }, review: { status: "unreviewed", passed_hash: null },
        proof: { state: "complete", sorry_count: 0 },
      }], edges: [] } as any;
      let calls = 0;
      const deps = { runCodex: async () => {
        calls++;
        return { stdout: JSON.stringify({ components: [] }), stderr: "" };
      } };
      const run = (crosswalk = baseCrosswalk, graph = baseGraph) => ensureComponentsForEnvs({
        envs, crosswalk, repoRoot: dir, leanSubdir: "Lean", cachePath, deps, graph,
      });

      await run();
      await run();
      expect(calls).toBe(1); // valid unchanged receipt
      await writeFile(candidatePath, "def CandidateA : Nat := 1\ndef CandidateB : Nat := 2\n", "utf8");
      await run();
      expect(calls).toBe(2); // canonical candidate inventory/source hash
      await writeFile(theoremPath, "theorem SourceThm : 1 = 1 := rfl\n", "utf8");
      await run();
      expect(calls).toBe(3); // authoritative source statement
      const driftCrosswalk: CrosswalkEntry[] = baseCrosswalk.map((c) =>
        c.obj_id === "A-1" ? { ...c, verdict: "drift" as const } : c);
      await run(driftCrosswalk);
      expect(calls).toBe(4); // crosswalk provenance
      await run(driftCrosswalk, { ...baseGraph, nodes: baseGraph.nodes.map((n: any) => ({
        ...n, review: { status: "matched", passed_hash: "abc" },
      })) });
      expect(calls).toBe(5); // graph provenance
    } finally { await rm(dir, { recursive: true, force: true }); }
  });
});

describe("component assembly trust boundary", () => {
  it("fails closed rather than auditing a partial component set", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "components-closed-"));
    try {
      await writeFile(path.join(dir, "Good.lean"), "lemma Good : True := trivial\n", "utf8");
      const modules = new Map<string, ModuleDecl>([["Good", { file: "Good.lean", decl: "Good", line: 1, kind: "lemma" }]]);
      await expect(assembleComponentText({
        specs: [{ type: "decl", decl: "Good" }, { type: "decl", decl: "Missing" }],
        crosswalk: [], moduleDecls: modules, repoRoot: dir, leanSubdir: ".",
      })).rejects.toThrow(/component Missing/);
    } finally { await rm(dir, { recursive: true, force: true }); }
  });

  it("returns the complete canonical resolved inventory used by the cache key", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "components-complete-"));
    try {
      await writeFile(path.join(dir, "Good.lean"), "lemma Good : True := trivial\n", "utf8");
      const assembled = await assembleComponentText({
        specs: [{ type: "decl", decl: "Good" }], crosswalk: [],
        moduleDecls: new Map([["Good", { file: "Good.lean", decl: "Good", line: 999, kind: "lemma" }]]),
        repoRoot: dir, leanSubdir: ".",
      });
      expect(assembled.resolved).toMatchObject([{ file: "Good.lean", decl: "Good", line: 1 }]);
      expect(assembled.text).toContain("lemma Good : True");
    } finally { await rm(dir, { recursive: true, force: true }); }
  });

  it("fails closed when only part of a requested binder set exists", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "components-binders-partial-"));
    try {
      await writeFile(path.join(dir, "Thm.lean"), "theorem Thm (H1 : True) : True := H1\n", "utf8");
      await expect(assembleComponentText({
        specs: [{ type: "hypotheses", theorem: "Thm", binders: ["H1", "H2"] }],
        crosswalk: [],
        moduleDecls: new Map([["Thm", { file: "Thm.lean", decl: "Thm", line: 1, kind: "theorem" }]]),
        repoRoot: dir, leanSubdir: ".",
      })).rejects.toThrow(/hypotheses \{H2\} are absent/);
    } finally { await rm(dir, { recursive: true, force: true }); }
  });

  it("fails closed when all requested binders are missing", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "components-binders-missing-"));
    try {
      await writeFile(path.join(dir, "Thm.lean"), "theorem Thm : True := trivial\n", "utf8");
      await expect(assembleComponentText({
        specs: [{ type: "hypotheses", theorem: "Thm", binders: ["H1", "H2"] }],
        crosswalk: [],
        moduleDecls: new Map([["Thm", { file: "Thm.lean", decl: "Thm", line: 1, kind: "theorem" }]]),
        repoRoot: dir, leanSubdir: ".",
      })).rejects.toThrow(/hypotheses \{H1, H2\} are absent/);
    } finally { await rm(dir, { recursive: true, force: true }); }
  });
});
