// Failing-test reproductions of the Phase-1 round-1 adversarial audit findings
// (2026-07-31), then kept as regression guards. One describe per finding.

import { describe, it, expect } from "vitest";
import { mkdtemp, mkdir, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { assembleCore } from "../../src/discovery/core/assemble.js";
import { normalizeWorkingState, saveWorkingState, loadWorkingState } from "../../src/discovery/stages/d0_working.js";
import type { Core } from "../../src/discovery/core/schema.js";
import type { WorkingState } from "../../src/discovery/stages/d0_working.js";

const core = (statements: Array<Record<string, unknown>>): Core =>
  ({
    qid: "q",
    symbols: [],
    assumptions: [],
    definitions: [],
    statements,
    bibliography: [],
    target_estimand: "tau",
  }) as unknown as Core;

const snap = (stmt: string) => ({ stmt, depends_on: [], defs: {}, assumptions: {} });

describe("F1: a frozen member with a settled status but a PARTIAL record renders open", () => {
  it("demotes an (anomalous) proved proto status to to-prove under a partial record", () => {
    // Unreachable through the current writers (GP2 forces all-to-prove at D-1.2;
    // apply composes prior.status) — defensive: were a proto ever to carry a
    // settled `proved`, a partial cursor record must win, or stale mathematics
    // publishes as established.
    const proto = core([
      { id: "thm:x", kind: "theorem", status: "proved", statement: "S", depends_on: [], proof_tex: "OLD" },
    ]);
    const out = assembleCore(proto, {
      round: 1,
      solved: { "thm:x": { proof_tex: "half", snapshot: snap("S"), partial: true } },
      resolved_oeqs: {},
    } as unknown as WorkingState);
    expect(out.statements[0].status).toBe("to-prove");
  });
});

describe("F2: invalidating an OEQ answer's record must not trip the save-boundary invariant", () => {
  it("a PARTIAL answer record satisfies normalizeWorkingState (the auto-heal marks partial, not delete)", () => {
    const w = {
      round: 3,
      solved: {
        "thm:answer": {
          proof_tex: "cites lem:missing",
          snapshot: snap("A"),
          node: { id: "thm:answer", kind: "theorem", statement: "A", depends_on: [], status: "to-prove" },
          partial: true,
        },
      },
      resolved_oeqs: { "oeq:q": { theorem_id: "thm:answer", source_fingerprint: "fp" } },
    } as unknown as WorkingState;
    expect(() => normalizeWorkingState(w)).not.toThrow();
    // ...whereas DELETING the record (the old heal behavior) is exactly the
    // unrepairable state the boundary refuses:
    delete w.solved["thm:answer"];
    expect(() => normalizeWorkingState(w)).toThrow(/thm:answer/);
  });
});

describe("F3: a fresh full record revives a pruned proto orphan", () => {
  it("does not filter a pruned_proto_orphans id that has a live non-partial record", () => {
    const proto = core([
      { id: "thm:root", kind: "theorem", status: "to-prove", statement: "R", depends_on: ["lem:l"] },
      { id: "lem:l", kind: "lemma", status: "to-prove", statement: "L", depends_on: [] },
    ]);
    const out = assembleCore(proto, {
      round: 5,
      solved: { "lem:l": { proof_tex: "fresh proof", snapshot: snap("L") } },
      resolved_oeqs: {},
      pruned_proto_orphans: ["lem:l"],
    } as unknown as WorkingState);
    const lem = out.statements.find((s) => s.id === "lem:l");
    expect(lem).toBeDefined();
    expect(lem!.status).toBe("proved");
  });

  it("still filters a pruned orphan with no record (or only shelved debt)", () => {
    const proto = core([
      { id: "thm:root", kind: "theorem", status: "to-prove", statement: "R", depends_on: [] },
      { id: "lem:l", kind: "lemma", status: "to-prove", statement: "L", depends_on: [] },
    ]);
    const out = assembleCore(proto, {
      round: 5,
      solved: {},
      resolved_oeqs: {},
      pruned_proto_orphans: ["lem:l"],
    } as unknown as WorkingState);
    expect(out.statements.find((s) => s.id === "lem:l")).toBeUndefined();
  });
});

describe("F5: cited-source attestation must not clobber unrelated published-core content", () => {
  // The CLI-level guarantee is asserted in orchestrator_state_clis-style e2e
  // runs; here we pin the contract the fix relies on: patching one node's
  // `source` in the published file leaves every other byte alone. (The re-render
  // approach failed exactly this: it rebuilt the WHOLE core from proto+working
  // and silently discarded D0.R's sanctioned in-place repairs.)
  it("in-place patch preserves sibling nodes not present in the working state", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "attest-f5-"));
    const published = core([
      { id: "lem:cited", kind: "lemma", status: "cited", statement: "C", depends_on: [],
        source: { cite: "K", locator: "Thm 1" } },
      // A D0.R-added repair lemma that exists ONLY in the published file.
      { id: "lem:d0r-repair", kind: "lemma", status: "proved", statement: "D", depends_on: [], proof_tex: "P" },
    ]);
    const p = path.join(tmp, "core.json");
    await mkdir(path.dirname(p), { recursive: true });
    await writeFile(p, JSON.stringify(published, null, 2), "utf8");
    // Simulate the fixed CLI: read, patch the one node, write back.
    const onDisk = JSON.parse(await readFile(p, "utf8")) as Core;
    const node = onDisk.statements.find((s) => s.id === "lem:cited")!;
    node.source = { ...node.source!, verbatim_statement: "The cited fact." };
    await writeFile(p, JSON.stringify(onDisk, null, 2), "utf8");
    const after = JSON.parse(await readFile(p, "utf8")) as Core;
    expect(after.statements.find((s) => s.id === "lem:d0r-repair")).toBeDefined();
    expect(after.statements.find((s) => s.id === "lem:cited")!.source!.verbatim_statement).toBe("The cited fact.");
  });
});

describe("R3F1: an answered source record can never publish, and the render sees the normalized cursor", () => {
  it("assembleCore skips an agent record whose id is an answered OEQ source", () => {
    // The legacy leftover state normalizeWorkingState repairs: the resolution AND
    // the historical source record both present. The render must not publish the
    // answered question even when handed the un-normalized cursor.
    const w = {
      round: 4,
      solved: {
        "oeq:q": {
          proof_tex: "",
          snapshot: snap("the question"),
          node: { id: "oeq:q", kind: "openendedquestion", statement: "the question", depends_on: [], status: "to-prove" },
        },
        "thm:answer": {
          proof_tex: "P",
          snapshot: snap("A"),
          node: { id: "thm:answer", kind: "theorem", statement: "A", depends_on: [], status: "proved" },
        },
      },
      resolved_oeqs: { "oeq:q": { theorem_id: "thm:answer", source_fingerprint: "fp" } },
    } as unknown as WorkingState;
    const out = assembleCore(core([]), w);
    expect(out.statements.some((s) => s.id === "oeq:q")).toBe(false);
    expect(out.statements.some((s) => s.id === "thm:answer")).toBe(true);
    // And after normalization (what the commit persists), the render is identical
    // — the published core cannot diverge from the saved cursor over this state.
    const before = JSON.stringify(out);
    normalizeWorkingState(w);
    expect(JSON.stringify(assembleCore(core([]), w))).toBe(before);
  });
});

describe("R2F2: the equivalence verdict is a FULL canonical comparison, not the compact diff", () => {
  it("catches a divergence in a field the compact diff does not enumerate", async () => {
    const { canonicalCoreJson, diffAssembledCore } = await import("../../src/discovery/replay.js");
    const a = core([{ id: "thm:x", kind: "theorem", status: "to-prove", statement: "S", depends_on: [] }]);
    const b = structuredClone(a);
    (b.definitions as unknown[]).push({ id: "def:d", name: "D", construction: "changed content" });
    // Same statement set and counts the compact diff enumerates...
    expect(diffAssembledCore(a, b)).toEqual([]);
    // ...but NOT equivalent — the canonical comparison is the gate.
    expect(canonicalCoreJson(a)).not.toBe(canonicalCoreJson(b));
  });
});

describe("F4: legacy-cursor read-compat for core-only checkpoint targets", () => {
  it("saveWorkingState does not stamp store_format (the legacy guard the recovery keys on)", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "f4-legacy-"));
    const ctx = { repoRoot: tmp, qid: "q_legacy", specialization: "v1", dryRun: false, resume: true };
    const dir = path.join(tmp, "doc", "research", "active", "q_legacy", "discovery");
    await mkdir(dir, { recursive: true });
    await saveWorkingState(ctx as never, {
      round: 1,
      solved: {},
      resolved_oeqs: {},
    } as unknown as WorkingState);
    const loaded = await loadWorkingState(ctx as never);
    expect(loaded?.store_format).toBeUndefined();
  });
});
