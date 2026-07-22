import { describe, it, expect } from "vitest";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { ensureComponentsForEnvs } from "../src/presentation/components.js";
import type { AnchoredEnv } from "../src/presentation/tex_anchors.js";
import type { CrosswalkEntry } from "../src/presentation/types.js";
import type { FormalizationGraph } from "../src/graph/types.js";

const env = (obj_id: string, e: AnchoredEnv["env"], order: number): AnchoredEnv => ({
  env: e,
  obj_id,
  title: null,
  body: `body of ${obj_id}`,
  order,
});
const cw = (obj_id: string, kind: string, decl: string | null): CrosswalkEntry => ({
  obj_id,
  kind,
  title: obj_id,
  tex: null,
  lean: decl ? { file: "Basic.lean", decl, decl_kind: "def", line: 0 } : null,
  verdict: "equivalent",
});
const defNode = (id: string, obj_id: string, decl: string): FormalizationGraph["nodes"][number] => ({
  id,
  obj_id,
  kind: "definition",
  provenance: "from-note",
  nl: { statement: id, tex_anchor: "", frozen: true },
  lean: { decl_name: decl, file: "Basic.lean" },
  review: { status: "matched", passed_hash: null },
  proof: { state: "complete", sorry_count: 0 },
});
const graph: FormalizationGraph = {
  qid: "q",
  specialization: "s",
  nodes: [defNode("def:a", "P-1", "declA"), defNode("def:h", "P-2", "declH")],
  edges: [{ kind: "statement-uses", from: "def:a", to: "def:h", source: "declared" }],
};

describe("ensureComponentsForEnvs graph-first", () => {
  it("uses graph component specs and does not call codex", async () => {
    const dir = mkdtempSync(join(tmpdir(), "comp-"));
    const throwingCodex = {
      runCodex: async () => {
        throw new Error("codex must not be called when graph specs exist");
      },
    };
    const { components } = await ensureComponentsForEnvs({
      envs: [env("P-1", "definitionv", 0)],
      crosswalk: [cw("P-1", "definition", "declA"), cw("P-2", "definition", "declH")],
      repoRoot: dir,
      leanSubdir: "nonexistent",
      cachePath: join(dir, "components_cache.json"),
      deps: throwingCodex,
      graph,
    });
    expect(components["P-1"]).toEqual([
      { type: "decl", decl: "declA" },
      { type: "decl", decl: "declH" },
    ]);
  });

  it("falls back to codex when the graph yields no specs for an env", async () => {
    const dir = mkdtempSync(join(tmpdir(), "comp-"));
    let called = 0;
    const fakeCodex = {
      runCodex: async () => {
        called++;
        return { stdout: JSON.stringify({ components: [{ type: "decl", decl: "discovered" }] }), stderr: "" };
      },
    };
    const { components } = await ensureComponentsForEnvs({
      envs: [env("X-9", "definitionv", 0)],
      crosswalk: [cw("X-9", "definition", null)], // no lean → graph gives []
      repoRoot: dir,
      leanSubdir: "nonexistent",
      cachePath: join(dir, "components_cache.json"),
      deps: fakeCodex,
      graph, // X-9 is not in the graph
    });
    expect(called).toBe(1);
    expect(components["X-9"]).toEqual([{ type: "decl", decl: "discovered" }]);
  });
});
