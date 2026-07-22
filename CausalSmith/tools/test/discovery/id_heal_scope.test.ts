// A non-kebab statement id is auto-healed (`lem:Ghat-x` -> `lem:ghat-x`). The rename must
// reach EVERY id-keyed store, not just core.statements: touching only the core left the
// working cursor keyed by the OLD id while the core carried the NEW one, so the two stores
// disagreed the instant a heal fired. Audit triage, 2026-07-20.

import { describe, it, expect, beforeAll, afterAll, beforeEach } from "vitest";
import { runStage0Solve } from "../../src/discovery/stages/d0_solve.js";
import { createDStageHarness, type DStageHarness } from "./d_stage_harness.js";
import type { StageDeps } from "../../src/pipeline_support.js";

const PROTO = {
  qid: "stat_heal", specialization: "v1", cluster: "stat",
  symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [{ id: "ass:overlap", kind: "support", condition: "c", free_symbols: [], standard: { name: "o", cite: "R1983" } }],
  definitions: [{ id: "def:env", name: "U", construction: "U = a", inputs: ["a"] }],
  statements: [{
    id: "thm:main", kind: "theorem", statement: "tau is identified",
    depends_on: ["ass:overlap"], status: "to-prove",
    justification: "j", gap: "g", consumer: "c",
  }],
  target_estimand: "tau", bibliography: [{ key: "R1983" }],
};

let h: DStageHarness;
beforeAll(async () => { h = await createDStageHarness({ qid: "stat_heal", specialization: "v1", proto: PROTO }); });
afterAll(async () => { await h.dispose(); });
beforeEach(async () => { await h.reset(); });

// Emits a helper whose id violates the lowercase-kebab grammar, and cites it.
const deps: StageDeps = {
  runCodex: async ({ prompt }: { prompt: string }) => {
    const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
    const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
    const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
    await writeFileSafe(outPath, JSON.stringify({
      proofs: targets.map((t) => ({ id: t.id, proof_tex: "By lem:Ghat-envelope, done." })),
      added_lemmas: [{
        id: "lem:Ghat-envelope", kind: "lemma", statement: "the envelope is valid",
        depends_on: [], status: "proved", proof_tex: "Envelope proof.",
      }],
    }));
    return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
  },
  runClaude: async () => { throw new Error("unused"); },
  lean: undefined as never,
};
async function writeFileSafe(p: string, body: string): Promise<void> {
  const { writeFile } = await import("node:fs/promises");
  await writeFile(p, body, "utf8");
}

describe("an auto-healed id is renamed in every store", () => {
  it("leaves no OLD key in the working cursor, and the core agrees", async () => {
    await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps });

    const working = await h.readWorking() as unknown as { solved: Record<string, { node?: { id: string } }> };
    const keys = Object.keys(working.solved ?? {});
    expect(keys, "the pre-heal id must not survive as a working key").not.toContain("lem:Ghat-envelope");
    expect(keys, "the healed id must be the working key").toContain("lem:ghat-envelope");

    // the embedded node must carry the healed id too, not just the map key
    const rec = working.solved["lem:ghat-envelope"];
    expect(rec?.node?.id ?? "lem:ghat-envelope").toBe("lem:ghat-envelope");

    // and the two stores must agree
    const core = await h.readCore();
    const coreIds = core.statements.map((s: { id: string }) => s.id);
    expect(coreIds).toContain("lem:ghat-envelope");
    expect(coreIds).not.toContain("lem:Ghat-envelope");
  }, 30000);
});

describe("the boundary heal renames PROOF ids too", () => {
  it("a proof keyed by the non-canonical id still lands on the healed node", async () => {
    // Renaming the statement but not the proof that targets it leaves the proof matching
    // no core statement: it is dropped as unmatched, and the node stays unproved.
    const proofDeps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const { writeFile } = await import("node:fs/promises");
        await writeFile(outPath, JSON.stringify({
          proofs: [
            ...targets.map((t) => ({ id: t.id, proof_tex: "By lem:Ghat-envelope, done." })),
            // keyed by the PRE-heal id
            { id: "lem:Ghat-envelope", proof_tex: "The envelope proof, supplied separately." },
          ],
          added_lemmas: [{
            id: "lem:Ghat-envelope", kind: "lemma", statement: "the envelope is valid",
            depends_on: [], status: "to-prove",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps: proofDeps });
    // The separately-supplied proof must have been matched to the healed node, so it is
    // NOT reported as naming no core statement.
    expect(String((result as { message?: string }).message ?? ""),
      "an unrenamed proof id shows up as a dropped, unmatched proof")
      .not.toMatch(/lem:Ghat-envelope/);

    const core = await h.readCore();
    const healed = core.statements.find((s: { id: string }) => s.id === "lem:ghat-envelope");
    expect(healed, "the healed node must exist").toBeDefined();
  }, 30000);
});

describe("the boundary heal covers obligations and prose notes", () => {
  it("renames an open_obligation node_id", async () => {
    // These are keyed by statement id too. Renaming the node but not the obligation left it
    // recorded under an id that no longer exists -- the round then halts asking for guidance
    // on a ghost node -- and left the prose note attached to nothing.
    const obligDeps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const { writeFile } = await import("node:fs/promises");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((t) => ({ id: t.id, proof_tex: "By lem:Ghat-envelope, done." })),
          added_lemmas: [{
            id: "lem:Ghat-envelope", kind: "lemma", statement: "the envelope is valid",
            depends_on: [], status: "to-prove",
          }],
          open_obligations: [{
            node_id: "lem:Ghat-envelope", what_is_open: "the envelope bound",
            obstruction: "needs a tail estimate", attempted: "a direct union bound",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps: obligDeps });
    const msg = String((result as { message?: string }).message ?? "");
    expect(msg, "no diagnostic may still name the PRE-heal id").not.toMatch(/lem:Ghat-envelope/);
  }, 30000);
});
