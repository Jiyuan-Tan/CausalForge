import { describe, it, expect, beforeAll, beforeEach, afterAll } from "vitest";
import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import {
  applyProposedChanges,
  parseProposalSelectors,
  validateProposalSelectors,
} from "../../src/discovery/stages/d0_apply.js";
import { protoCoreJsonPath } from "../../src/discovery/stages/neg1_2_author.js";
import { workingPath } from "../../src/discovery/stages/d0_working.js";
import type { PipelineContext } from "../../src/types.js";

const QID = "stat_selectortest";
const SPEC = "v1";

const PROTO = {
  qid: QID,
  specialization: SPEC,
  cluster: "stat",
  symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [
    {
      id: "ass:overlap",
      kind: "support",
      condition: "the propensity is bounded away from 0 and 1",
      free_symbols: [],
      standard: { name: "overlap", cite: "Rosenbaum1983" },
    },
  ],
  definitions: [{ id: "def:env", name: "U", construction: "U = a", inputs: ["a"] }],
  statements: [
    {
      id: "thm:main",
      kind: "theorem",
      statement: "tau is identified",
      depends_on: ["ass:overlap"],
      status: "to-prove",
      justification: "core ID",
      gap: "vs prior",
      consumer: "applied",
    },
  ],
  target_estimand: "tau = E[Y(1) - Y(0)]",
  bibliography: [{ key: "Rosenbaum1983" }],
};

let repoRoot: string;

function makeCtx(root: string): PipelineContext {
  return { repoRoot: root, qid: QID, specialization: SPEC, dryRun: false, resume: false };
}

/** Seed the round's proposals on the SOLE carrier (`d0_working.json:proposals`). */
async function seedProposals(
  ctx: PipelineContext,
  proposals: Partial<{ statements: unknown[]; definitions: unknown[]; assumptions: unknown[]; coreEdits: unknown[]; proofs: unknown[] }>,
): Promise<void> {
  await mkdir(path.dirname(workingPath(ctx)), { recursive: true });
  await writeFile(
    workingPath(ctx),
    JSON.stringify({
      round: 1,
      solved: {},
      proposals: {
        statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [],
        ...proposals,
      },
    }),
    "utf8",
  );
}

/** The collision this whole feature exists for: ONE round proposing a claim change
 *  AND a metadata-only `statement-replace` on the SAME node. The core edit echoes
 *  the CURRENT statement/status byte-for-byte, carries no proof text, and puts the
 *  real payload in `depends_on`. */
async function seedCollidingProposals(ctx: PipelineContext): Promise<void> {
  await seedProposals(ctx, {
    statements: [
      {
        id: "thm:main",
        current: "tau is identified",
        proposed: "tau is identified on the overlap region",
        reason: "too strong without overlap on full support",
        direction: "narrow",
      },
    ],
    coreEdits: [
      {
        kind: "statement-replace",
        id: "thm:main",
        proposed: {
          id: "thm:main",
          kind: "theorem",
          statement: "tau is identified",
          depends_on: ["ass:overlap", "def:env"],
          status: "to-prove",
          justification: "core ID",
          gap: "vs prior",
          consumer: "applied",
        },
        reason: "thm:main actually uses def:env",
        direction: "correct",
      },
    ],
  });
}

beforeAll(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "cs-selector-"));
});
afterAll(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});
beforeEach(async () => {
  const ctx = makeCtx(repoRoot);
  await mkdir(path.dirname(protoCoreJsonPath(ctx)), { recursive: true });
  await writeFile(protoCoreJsonPath(ctx), JSON.stringify(PROTO), "utf8");
  await rm(workingPath(ctx), { force: true });
});

describe("parseProposalSelectors", () => {
  it("treats a BARE id as every channel, preserving the pre-qualifier behaviour", () => {
    const sel = parseProposalSelectors(["thm:main"]);
    expect(sel.matchesStatement("thm:main")).toBe(true);
    expect(sel.matchesCoreEdit({ kind: "statement-replace", id: "thm:main" } as never)).toBe(true);
    expect(sel.unmatched()).toEqual([]);
  });

  it("a CHANNEL qualifier selects that channel and excludes the other", () => {
    const stmt = parseProposalSelectors(["statement:thm:main"]);
    expect(stmt.matchesStatement("thm:main")).toBe(true);
    expect(stmt.matchesCoreEdit({ kind: "statement-replace", id: "thm:main" } as never)).toBe(false);

    const edit = parseProposalSelectors(["core-edit:thm:main"]);
    expect(edit.matchesStatement("thm:main")).toBe(false);
    expect(edit.matchesCoreEdit({ kind: "statement-replace", id: "thm:main" } as never)).toBe(true);
  });

  it("a CORE-EDIT-KIND qualifier discriminates two edits sharing one target", () => {
    const sel = parseProposalSelectors(["statement-replace:thm:main"]);
    expect(sel.matchesCoreEdit({ kind: "statement-replace", id: "thm:main" } as never)).toBe(true);
    expect(sel.matchesCoreEdit({ kind: "statement-delete", id: "thm:main" } as never)).toBe(false);
    expect(sel.matchesStatement("thm:main")).toBe(false);
  });

  it("recognizes assumption-delete as a kind-qualified adjudication selector", () => {
    const sel = parseProposalSelectors(["assumption-delete:ass:overlap"]);
    expect(sel.matchesCoreEdit({ kind: "assumption-delete", id: "ass:overlap" } as never)).toBe(true);
    expect(sel.matchesCoreEdit({ kind: "assumption-replace", id: "ass:overlap" } as never)).toBe(false);
    expect(sel.unmatched()).toEqual([]);
  });

  it("keeps colons inside the id half, including LaTeX symbol and bib targets", () => {
    const sel = parseProposalSelectors([
      "core-edit:sym:\\(\\bar{\\mathcal C}_{n,\\alpha}^d\\)",
      "bibliography-replace:bib:Rosenbaum1983",
    ]);
    expect(sel.matchesCoreEdit({ kind: "symbol-replace", name: "\\(\\bar{\\mathcal C}_{n,\\alpha}^d\\)" } as never)).toBe(true);
    expect(sel.matchesCoreEdit({ kind: "bibliography-replace", key: "Rosenbaum1983" } as never)).toBe(true);
    expect(sel.unmatched()).toEqual([]);
  });

  it("does not mistake a node id whose prefix resembles a qualifier", () => {
    // `metadata:reverse-dependencies` is a real core-edit TARGET, not a qualified selector.
    const sel = parseProposalSelectors(["metadata:reverse-dependencies"]);
    expect(
      sel.matchesCoreEdit({ kind: "rebuild-reverse-dependencies", id: "metadata:reverse-dependencies" } as never),
    ).toBe(true);
  });

  it("reports selectors that matched nothing, per channel", () => {
    const sel = parseProposalSelectors(["core-edit:thm:main", "statement:thm:ghost"]);
    sel.matchesStatement("thm:main"); // wrong channel for selector 1, no such id for selector 2
    expect(sel.unmatched()).toEqual(["core-edit:thm:main", "statement:thm:ghost"]);
    sel.matchesCoreEdit({ kind: "statement-replace", id: "thm:main" } as never);
    expect(sel.unmatched()).toEqual(["statement:thm:ghost"]);
  });
});

describe("validateProposalSelectors", () => {
  it("rejects a doubly-qualified selector, which could never match", () => {
    expect(validateProposalSelectors(["statement:core-edit:thm:main"])).toEqual(["statement:core-edit:thm:main"]);
  });
  it("accepts bare and singly-qualified selectors", () => {
    expect(validateProposalSelectors(["thm:main", "statement:thm:main", "bib:Key"])).toEqual([]);
  });
});

describe("applyProposedChanges with a kind-qualified selector", () => {
  it("applies ONLY the claim change when the round also proposes a core edit on that node", async () => {
    const ctx = makeCtx(repoRoot);
    await seedCollidingProposals(ctx);

    const changed = await applyProposedChanges({
      ctx,
      ids: parseProposalSelectors(["statement:thm:main"]),
      note: "accept the narrowing, defer the rewiring",
    });

    expect(changed).toHaveLength(1);
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const thm = proto.statements.find((s: { id: string }) => s.id === "thm:main");
    expect(thm.statement).toBe("tau is identified on the overlap region");
    expect(thm.depends_on).toEqual(["ass:overlap"]); // the core edit was NOT applied
  });

  it("applies ONLY the core edit under the complementary selector", async () => {
    const ctx = makeCtx(repoRoot);
    await seedCollidingProposals(ctx);

    const changed = await applyProposedChanges({
      ctx,
      ids: parseProposalSelectors(["core-edit:thm:main"]),
      note: "accept the rewiring, defer the narrowing",
    });

    expect(changed).toHaveLength(1);
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const thm = proto.statements.find((s: { id: string }) => s.id === "thm:main");
    expect(thm.depends_on).toEqual(["ass:overlap", "def:env"]);
    expect(thm.statement).toBe("tau is identified"); // the claim change was NOT applied
  });

  // A cited node's empty durable proof remains authoritative when metadata is replaced.
  it("preserves an omitted carried proof while replacing cited metadata", async () => {
    const ctx = makeCtx(repoRoot);
    const workingP = workingPath(ctx);
    await writeFile(
      workingP,
      JSON.stringify({
        round: 1,
        escalation_entries_consumed: 0,
        solved: {
          "lem:cited": {
            proof_tex: "",
            snapshot: { stmt: "Author shows X.", depends_on: [], defs: {}, assumptions: {} },
            node: {
              id: "lem:cited",
              kind: "lemma",
              statement: "Author shows X.",
              depends_on: [],
              status: "cited",
              proof_tex: "",
              source: { cite: "Rosenbaum1983", locator: "stale locator" },
            },
          },
        },
        proposals: {
          statements: [], definitions: [], assumptions: [], proofs: [],
          coreEdits: [
            {
              kind: "statement-replace",
              id: "lem:cited",
              proposed: {
                id: "lem:cited",
                kind: "lemma",
                statement: "Author shows X.",
                depends_on: [],
                status: "cited",
                // proof_tex intentionally ABSENT — this is what the solver emits.
                source: { cite: "Rosenbaum1983", locator: "corrected locator" },
              },
              reason: "repair the source locator on a cited leaf",
              direction: "correct",
            },
          ],
        },
      }),
      "utf8",
    );

    const changed = await applyProposedChanges({ ctx, ids: new Set(["lem:cited"]), note: "source repair" });

    expect(changed).toHaveLength(1);
    const working = JSON.parse(await readFile(workingP, "utf8"));
    expect(working.solved["lem:cited"].node.source.locator).toBe("corrected locator");
    expect(working.solved["lem:cited"].partial).toBeUndefined(); // a cited leaf stays discharged
  });

  // A statement-replace never changes claim text (the echo guarantees it), so a proof the
  // SAME round emitted for that node was written against exactly this rewiring. Landing
  // the edit and discarding the proof costs a whole solve round re-confirming it.
  async function seedRewiringWithPairedProof(
    ctx: PipelineContext,
    opts: { depValid: boolean },
  ): Promise<void> {
    await writeFile(
      workingPath(ctx),
      JSON.stringify({
        round: 1,
        escalation_entries_consumed: 0,
        solved: {
          "lem:dep": {
            proof_tex: "Dep proof.",
            ...(opts.depValid ? {} : { partial: true }),
            snapshot: { stmt: "A dependency.", depends_on: [], defs: {}, assumptions: {} },
            node: { id: "lem:dep", kind: "lemma", statement: "A dependency.", depends_on: [], status: "proved", proof_tex: "Dep proof." },
          },
          "lem:rewired": {
            proof_tex: "Old proof citing nothing.",
            partial: true,
            snapshot: { stmt: "A rewired claim.", depends_on: [], defs: {}, assumptions: {} },
            node: { id: "lem:rewired", kind: "lemma", statement: "A rewired claim.", depends_on: [], status: "to-prove" },
          },
        },
        proposals: {
          statements: [],
          definitions: [],
          assumptions: [],
          coreEdits: [
            {
              kind: "statement-replace",
              id: "lem:rewired",
              proposed: {
                id: "lem:rewired",
                kind: "lemma",
                statement: "A rewired claim.",
                depends_on: ["lem:dep"],
                status: "to-prove",
              },
              reason: "rewire onto the dependency it actually uses",
              direction: "correct",
            },
          ],
          proofs: [{ id: "lem:rewired", proof_tex: "New proof, via lem:dep." }],
        },
      }),
      "utf8",
    );
  }

  it("commits a paired proof with the rewiring instead of discarding it", async () => {
    const ctx = makeCtx(repoRoot);
    await seedRewiringWithPairedProof(ctx, { depValid: true });

    await applyProposedChanges({ ctx, ids: new Set(["lem:rewired"]), note: "rewire + proof" });

    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    const rec = working.solved["lem:rewired"];
    expect(rec.node.depends_on).toEqual(["lem:dep"]);
    expect(rec.node.status).toBe("proved");
    expect(rec.proof_tex).toBe("New proof, via lem:dep.");
    expect(rec.partial).toBeUndefined(); // no re-solve round owed
    expect(rec.snapshot.depends_on).toEqual(["lem:dep"]); // snapshot recomputed, so it stays valid
  });

  it("REFUSES to clear partial when the rewired closure is itself stale", async () => {
    const ctx = makeCtx(repoRoot);
    await seedRewiringWithPairedProof(ctx, { depValid: false }); // lem:dep is partial

    await applyProposedChanges({ ctx, ids: new Set(["lem:rewired"]), note: "rewire onto a stale dep" });

    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    const rec = working.solved["lem:rewired"];
    expect(rec.node.depends_on).toEqual(["lem:dep"]); // the rewiring still lands
    expect(rec.partial).toBe(true); // but the proof is NOT certified against a stale closure
    expect(rec.node.status).toBe("to-prove");
  });

  it("a BARE id still selects both, so existing call sites are unaffected", async () => {
    const ctx = makeCtx(repoRoot);
    await seedCollidingProposals(ctx);

    const changed = await applyProposedChanges({ ctx, ids: new Set(["thm:main"]), note: "both" });

    expect(changed).toHaveLength(2);
  });
});

describe("applyProposedChanges assumption deletion", () => {
  it("applies an assumption deletion only after the same bundle removes its live premise edge", async () => {
    const ctx = makeCtx(repoRoot);
    await seedProposals(ctx, {
      coreEdits: [
        {
          kind: "assumption-delete",
          id: "ass:overlap",
          reason: "the premise is no longer used",
          direction: "delete-obsolete",
        },
        {
          kind: "statement-replace",
          id: "thm:main",
          proposed: { ...PROTO.statements[0], depends_on: [] },
          reason: "the repaired proof establishes the theorem without overlap",
          direction: "correct",
        },
      ],
    });

    const changed = await applyProposedChanges({ ctx });
    expect(changed.map((entry) => entry.id)).toEqual(["thm:main", "ass:overlap"]);
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(proto.assumptions).toEqual([]);
    expect(proto.statements[0].depends_on).toEqual([]);
  });

  it("refuses to delete an assumption while a statement still depends on it", async () => {
    const ctx = makeCtx(repoRoot);
    await seedProposals(ctx, {
      coreEdits: [{
        kind: "assumption-delete",
        id: "ass:overlap",
        reason: "premature deletion",
        direction: "delete-obsolete",
      }],
    });
    const before = await readFile(protoCoreJsonPath(ctx), "utf8");

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/Cannot delete assumption ass:overlap.*thm:main\.depends_on/);
    expect(await readFile(protoCoreJsonPath(ctx), "utf8")).toBe(before);
  });
});
