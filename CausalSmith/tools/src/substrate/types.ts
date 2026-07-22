// CausalSmith/tools/src/substrate/types.ts
import { z } from "zod";

export type SubstratePhase =
  // `coordinate` is the intelligent successor of the mechanical `promote` phase:
  // on reviewer PASS a codex coordinator places + dedups + records the substrate
  // into Causalean, then the deterministic verify-or-rollback gate runs. The
  // legacy `promote` value is retained so an in-flight run's state.json still
  // parses (the pipeline treats it as `coordinate`).
  | "build" | "fill" | "review" | "coordinate" | "promote" | "done" | "escalated" | "halted";

export const codexPromptSchema = z.object({
  id: z.string(),
  target_decls: z.array(z.string()).default([]),
  prompt: z.string(),
});
export type CodexPrompt = z.infer<typeof codexPromptSchema>;

export const scaffolderOutputSchema = z.object({
  decision: z.enum(["build", "review", "escalate"]),
  plan_markdown: z.string(),
  codex_prompts: z.array(codexPromptSchema).default([]),
  escalation: z.object({ reason: z.string() }).optional(),
});
export type ScaffolderOutput = z.infer<typeof scaffolderOutputSchema>;
export function parseScaffolderOutput(value: unknown): ScaffolderOutput {
  return scaffolderOutputSchema.parse(value);
}

export interface FillerReport { id: string; ok: boolean; summary: string }

export interface BuildDiagnostics {
  ok: boolean;
  errors: string[];
  sorryCount: number;
  perFile: Record<string, { sorries: number; errors: number }>;
}

export interface RoundReport {
  round: number;
  fillers: FillerReport[];
  build: BuildDiagnostics;
}

export const reviewVerdictSchema = z.object({
  pass: z.boolean(),
  // Tolerate the shapes the reviewer model actually emits: a single string, a
  // list of finding strings/objects (codex often returns `findings: []` on a
  // clean pass), or null. Normalize everything to one newline-joined string so
  // a benign shape difference never crashes the run.
  findings: z
    .union([z.string(), z.array(z.any()), z.null()])
    .transform((v) =>
      v == null
        ? ""
        : Array.isArray(v)
          ? v.map((x) => (typeof x === "string" ? x : JSON.stringify(x))).join("\n")
          : v,
    ),
  checks: z.object({
    generic: z.boolean(),
    reusable: z.boolean(),
    standard: z.boolean(),
    not_vacuous: z.boolean(),
    fulfills_goal: z.boolean(),
    sorry_free: z.boolean(),
    layered: z.boolean(),
  }),
}).superRefine((verdict, ctx) => {
  const checksPass = Object.values(verdict.checks).every(Boolean);
  // why: a reviewer PASS is only coherent when every required check passes.
  if (verdict.pass !== checksPass) {
    ctx.addIssue({
      code: z.ZodIssueCode.custom,
      path: ["pass"],
      message: "pass must equal Object.values(checks).every(Boolean)",
    });
  }
});
export type ReviewVerdict = z.infer<typeof reviewVerdictSchema>;
export function parseReviewVerdict(value: unknown): ReviewVerdict {
  return reviewVerdictSchema.parse(value);
}

const buildDiagnosticsSchema = z.object({
  ok: z.boolean(),
  errors: z.array(z.string()),
  sorryCount: z.number().int().nonnegative(),
  perFile: z.record(z.object({ sorries: z.number(), errors: z.number() })),
});
const roundReportSchema = z.object({
  round: z.number().int().nonnegative(),
  fillers: z.array(z.object({ id: z.string(), ok: z.boolean(), summary: z.string() })),
  build: buildDiagnosticsSchema,
});

export const substrateStateSchema = z.object({
  slug: z.string(),
  phase: z.enum(["build", "fill", "review", "coordinate", "promote", "done", "escalated", "halted"]),
  buildRounds: z.number().int().nonnegative().default(0),
  reviewRounds: z.number().int().nonnegative().default(0),
  // Bounded retry budget for the `coordinate` phase (mirrors reviewRounds): each
  // failed integration gate feeds its log back to the coordinator for another
  // attempt, up to COORD_CAP.
  coordinateRounds: z.number().int().nonnegative().default(0),
  lastCoordinateLog: z.union([z.string(), z.null()]).default(null),
  moduleFiles: z.array(z.string()).default([]),
  // The scaffolder's filler prompts for the current round, persisted at the
  // scaffold→fill checkpoint so a resume re-enters the (codex) proof-fill stage
  // WITHOUT re-running the expensive scaffolder. Cleared once consumed.
  pendingPrompts: z.array(codexPromptSchema).default([]),
  lastReport: z.union([roundReportSchema, z.null()]).default(null),
  lastReview: z.union([reviewVerdictSchema, z.null()]).default(null),
  // `legacy-unreviewed` means the persisted verdict predates the dependency-
  // layering check. It is never upgraded to a pass without a fresh review.
  layeringReviewStatus: z.enum(["current", "legacy-unreviewed"]).default("current"),
  terminalMessage: z.union([z.string(), z.null()]).default(null),
});
export type SubstrateState = z.infer<typeof substrateStateSchema>;

// JSON Schemas for runClaude({ jsonSchema }).
export const SCAFFOLDER_JSON_SCHEMA = {
  type: "object",
  required: ["decision", "plan_markdown"],
  properties: {
    decision: { type: "string", enum: ["build", "review", "escalate"] },
    plan_markdown: { type: "string" },
    codex_prompts: {
      type: "array",
      items: {
        type: "object",
        required: ["id", "prompt"],
        properties: {
          id: { type: "string" },
          target_decls: { type: "array", items: { type: "string" } },
          prompt: { type: "string" },
        },
      },
    },
    escalation: {
      type: "object",
      required: ["reason"],
      properties: { reason: { type: "string" } },
    },
  },
} as const;

// --- Coordinator manifest (the codex coordinator's structured output) ---------
//
// PARSE-SAFETY BY DESIGN: the manifest carries NO file contents. Large,
// heavily-escaped Lean bodies inside JSON were the dominant parse-failure mode
// (truncated string literals defeat brace-balance repair). Instead the
// coordinator WRITES each body / insert patch to a file under the STAGING dir
// and the manifest references it by `from` (a short relative path). Every op
// therefore holds only tiny metadata — destination path, a short anchor line,
// the staged-source path — so the JSON stays a few hundred bytes and parses
// reliably. The deterministic apply layer reads `from` off disk.
//
// Destinations (`target`) are relative to the Causalean root (the dir holding
// `Causalean.lean`); `from` is relative to the staging dir. Three op kinds:
//
//   - create_file  a brand-new file (a fresh Lean module, or a sidecar / doc
//                  record). `newModule` (Lean modules only) is root-wired into
//                  `Causalean.lean`.
//   - merge_lean   an INSERT-ONLY patch into an existing Lean file: the staged
//                  content goes in after the line containing `anchor` (empty =
//                  append at end of file). The apply layer asserts
//                  byte-preservation, so a merge can never alter a proven decl.
//   - write_file   full-content write of a NON-Lean derived/record file (headline
//                  sidecar JSON, `doc/API.md`). Snapshot+rollback protected, but
//                  not subject to the insert-only Lean invariant (these are
//                  derived/narrative surfaces guarded by doc:check / the index).
export const coordOpSchema = z.discriminatedUnion("kind", [
  z.object({
    kind: z.literal("create_file"),
    target: z.string(),
    from: z.string(),
    newModule: z.string().optional(),
  }),
  z.object({
    kind: z.literal("merge_lean"),
    target: z.string(),
    anchor: z.string().default(""),
    from: z.string(),
  }),
  z.object({
    kind: z.literal("write_file"),
    target: z.string(),
    from: z.string(),
  }),
]);
export type CoordOp = z.infer<typeof coordOpSchema>;

export const coordinationManifestSchema = z.object({
  ops: z.array(coordOpSchema).min(1),
  // Free-form rationale for the run log (placement decisions, dedup notes).
  notes: z.string().default(""),
});
export type CoordinationManifest = z.infer<typeof coordinationManifestSchema>;
export function parseCoordinationManifest(value: unknown): CoordinationManifest {
  return coordinationManifestSchema.parse(value);
}

export const REVIEW_JSON_SCHEMA = {
  type: "object",
  required: ["pass", "findings", "checks"],
  properties: {
    pass: { type: "boolean" },
    findings: { type: "string" },
    checks: {
      type: "object",
      required: ["generic", "reusable", "standard", "not_vacuous", "fulfills_goal", "sorry_free", "layered"],
      properties: {
        generic: { type: "boolean" },
        reusable: { type: "boolean" },
        standard: { type: "boolean" },
        not_vacuous: { type: "boolean" },
        fulfills_goal: { type: "boolean" },
        sorry_free: { type: "boolean" },
        layered: { type: "boolean" },
      },
    },
  },
} as const;
