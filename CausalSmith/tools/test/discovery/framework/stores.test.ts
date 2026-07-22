import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import os from "node:os";
import { stores, WorkingStateSchema } from "../../../src/discovery/framework/stores.js";
import type { PipelineContext } from "../../../src/types.js";

let tmp: string;
let ctx: PipelineContext;

beforeEach(async () => {
  tmp = await mkdtemp(path.join(os.tmpdir(), "stores-test-"));
  ctx = { repoRoot: tmp, qid: "stat_demo", specialization: "econometrics", dryRun: false, resume: false } as PipelineContext;
});
afterEach(async () => {
  await rm(tmp, { recursive: true, force: true });
});

function qidDir(...rest: string[]): string {
  // research qids live under <repoRoot>/doc/research/active/<qid>/ (paths.ts formalizationDir)
  return path.join(tmp, "doc", "research", "active", "stat_demo", ...rest);
}

describe("stores registry", () => {
  it("resolves canonical nested paths for fresh runs", () => {
    expect(stores.protoCore.path(ctx)).toBe(qidDir("discovery", "proto_core.json"));
    expect(stores.core.path(ctx)).toBe(qidDir("discovery", "core.json"));
    expect(stores.working.path(ctx)).toBe(qidDir("discovery", "d0_working.json"));
    expect(stores.gaps.path(ctx)).toBe(qidDir("discovery", "gaps.json"));
  });

  it("prefers an existing legacy-prefixed file (pre-migration run)", async () => {
    await mkdir(qidDir("discovery"), { recursive: true });
    const legacy = qidDir("discovery", "stat_demo_d0_working.json");
    await writeFile(legacy, JSON.stringify({ round: 1, solved: {} }), "utf8");
    expect(stores.working.path(ctx)).toBe(legacy);
    expect(await stores.working.load(ctx)).toMatchObject({ round: 1 });
  });

  it("WorkingStateSchema accepts a realistic working state and preserves unknown fields", () => {
    const w = {
      round: 4,
      proposal_revision: "angle:0/version:2",
      solved: {
        "thm:main": { proof_tex: "p", snapshot: { stmt: "s", defs: {}, assumptions: {} } },
        "lem:helper": {
          proof_tex: "q",
          snapshot: { stmt: "t", depends_on: ["def:x"], defs: { "def:x": "c" }, assumptions: {} },
          node: { id: "lem:helper", kind: "lemma", statement: "t", status: "proved" },
          owner: "unit-a",
          partial: false,
        },
      },
      proposals: {
        statements: [],
        definitions: [],
        assumptions: [],
        coreEdits: [{ kind: "statement-delete", id: "conj:z" }],
        proofs: [{ id: "thm:main", proof_tex: "p" }],
      },
      resolved_oeqs: { "oeq:q1": { theorem_id: "thm:main", source_fingerprint: "fp" }, "oeq:q0": "thm:old" },
      some_future_field: { kept: true },
    };
    const parsed = WorkingStateSchema.parse(w);
    expect(parsed.round).toBe(4);
    expect((parsed as Record<string, unknown>).some_future_field).toEqual({ kept: true });
  });

  it("WorkingStateSchema rejects a working state missing `solved`", () => {
    expect(() => WorkingStateSchema.parse({ round: 1 })).toThrow();
  });
});
