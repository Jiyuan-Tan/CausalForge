// Phase-0 store registry. Each store's canonical + legacy name is declared ONCE
// here. Stores whose owning stage is not yet ported (reviews, manifests,
// obligations, packets) are added by that stage's port — keep this list an
// exact mirror of what ported code actually touches.
import { z } from "zod";
import { artifactPath, gapsJsonPath } from "../../paths.js";
import { CoreSchema } from "../core/schema.js";
import { defineJsonStore } from "./store.js";
import type { PipelineContext } from "../../types.js";

/** Zod boundary for `d0_working.json` — first-ever validation of this store.
 *  Deliberately `.passthrough()` at every level: the schema asserts the
 *  load-bearing shape (round, solved records, proposal payload arrays) without
 *  freezing forward-compatible extras. Mirrors `WorkingState` in
 *  `stage0_working.ts`; that interface remains the compile-time face until the
 *  D0 port unifies them. */
const MemberSnapshotSchema = z
  .object({
    stmt: z.string(),
    depends_on: z.array(z.string()).optional(),
    defs: z.record(z.string()),
    assumptions: z.record(z.string()),
  })
  .passthrough();

const SolvedMemberSchema = z
  .object({
    proof_tex: z.string(),
    snapshot: MemberSnapshotSchema,
    node: z.object({ id: z.string() }).passthrough().optional(),
    owner: z.string().optional(),
    partial: z.boolean().optional(),
  })
  .passthrough();

export const WorkingStateSchema = z
  .object({
    round: z.number(),
    escalation_entries_consumed: z.number().optional(),
    proposal_revision: z.string().optional(),
    solved: z.record(SolvedMemberSchema),
    proposals: z
      .object({
        statements: z.array(z.unknown()),
        definitions: z.array(z.unknown()),
        assumptions: z.array(z.unknown()),
        coreEdits: z.array(z.unknown()),
        proofs: z.array(z.object({ id: z.string(), proof_tex: z.string() }).passthrough()),
      })
      .passthrough()
      .optional(),
    resolved_oeqs: z
      .record(
        z.union([z.object({ theorem_id: z.string(), source_fingerprint: z.string() }).passthrough(), z.string()]),
      )
      .optional(),
  })
  .passthrough();
export type ValidatedWorkingState = z.infer<typeof WorkingStateSchema>;

/** Minimal shape of `gaps.json` (authored by the D-1.1 scout agent). */
export const GapsFileSchema = z
  .object({
    status: z.string().optional(),
    n_open_problems: z.number().optional(),
    open_problems: z.array(z.unknown()).optional(),
  })
  .passthrough();

const discovery = (ctx: PipelineContext, name: string): string =>
  artifactPath(ctx.repoRoot, ctx.qid, "discovery", name, [`${ctx.qid}_${name}`]);

export const stores = {
  /** Frozen D-1.2 proposal core — the freeze baseline. */
  protoCore: defineJsonStore({
    id: "proto_core",
    resolve: (ctx) => discovery(ctx, "proto_core.json"),
    schema: CoreSchema,
  }),
  /** Derived solved core. */
  core: defineJsonStore({ id: "core", resolve: (ctx) => discovery(ctx, "core.json"), schema: CoreSchema }),
  /** D0 incremental working cursor (proofs + this round's proposal payload). */
  working: defineJsonStore({
    id: "d0_working",
    resolve: (ctx) => discovery(ctx, "d0_working.json"),
    schema: WorkingStateSchema,
  }),
  /** D-1.1 literature-scout output. Note: legacy name uses the run prefix, so this
   *  resolver delegates to the existing `gapsJsonPath` (which knows it). */
  gaps: defineJsonStore({
    id: "gaps",
    resolve: (ctx) => gapsJsonPath(ctx.repoRoot, ctx.qid, ctx.specialization),
    schema: GapsFileSchema,
  }),
} as const;
