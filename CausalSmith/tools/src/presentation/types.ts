import { z } from "zod";

/** Shared schemas for CausalSmith presentation mode. */

export const CrosswalkLean = z.object({
  file: z.string(),
  decl: z.string(),
  decl_kind: z.string(),
  line: z.number(),
});
export type CrosswalkLean = z.infer<typeof CrosswalkLean>;

export const CrosswalkEntry = z.object({
  obj_id: z.string(),
  kind: z.string(),
  title: z.string(),
  tex: z.object({ label: z.string(), line_range: z.string() }).nullable(),
  lean: CrosswalkLean.nullable(),
  verdict: z.string(),
});
export type CrosswalkEntry = z.infer<typeof CrosswalkEntry>;
export const Crosswalk = z.array(CrosswalkEntry);

export const PaperStage = z.enum(["P0", "P1", "P2", "P3", "P4", "P5"]);
export type PaperStage = z.infer<typeof PaperStage>;

export const PaperState = z.object({
  qid: z.string(),
  spec: z.string(),
  stage_completed: PaperStage.nullable(),
  checkpoint_pending: z.enum(["outline", "draft"]).nullable(),
  pinned_commit: z.string().nullable(),
  revision_round: z.number().int(),
  /** Number of holistic P5-driven manuscript revision passes already attempted (hard cap: 2). */
  p5_revision_passes: z.number().int().nonnegative().default(0),
  /** Repairable P5 issue families supplied to the immediately preceding holistic pass. */
  p5_last_fingerprints: z.array(z.string()).default([]),
  hard_gate_failures: z.array(z.object({ gate: z.string(), detail: z.string() })),
  notes: z.array(z.string()),
});
export type PaperState = z.infer<typeof PaperState>;

// ---------------------------------------------------------------------------
// Bundle outputs (the pipeline↔site contract)

export const PresentationEntry = z.object({
  obj_id: z.string(),
  // "prose" ⇒ a from-note object presented only in the narrative (no formal block), reachable
  // via an inline \leanref. "citedv" ⇒ a source-matched external result, web-only because its
  // consumer carries the scope disclosure. "auxiliary" ⇒ an agent-introduced proof helper,
  // web-only (no body block, no NL). "symbol" ⇒ a core symbol's Lean realization cluster (the
  // `@realizes <sym>` tags), web-only — surfaced in the Formal-layer panel's symbol group. All
  // open the drawer.
  env: z.enum(["theoremv", "assumptionv", "lemmav", "definitionv", "citedv", "propositionv", "remarkv", "prose", "auxiliary", "symbol"]),
  paper_label: z.string(), // e.g. "Theorem 2"
  title: z.string().nullable(),
  lean: CrosswalkLean.nullable(), // null ⇒ drawer shows `fallback`
  fallback: z.string().nullable(), // e.g. "stated as hypothesis H2 of t1_thm"
  uses: z.array(z.string()).default([]), // obj_ids of assumptions/definitions this theorem draws on
  // causalsmith review verdict for this object, carried verbatim so the page never presents an
  // unverified/drifted object as verified. Defaults keep old bundles parseable.
  status: z.string().default("unreviewed"),
  sorry_free: z.boolean().nullable().default(null),
});
export type PresentationEntry = z.infer<typeof PresentationEntry>;

export const PresentationCrosswalk = z.object({
  commit: z.string(),
  lean_subdir: z.string(), // repo-relative dir of the Lean files
  entries: z.array(PresentationEntry),
});
export type PresentationCrosswalk = z.infer<typeof PresentationCrosswalk>;

export const LeanSnippet = z.object({
  decl: z.string(),
  file: z.string(),
  line: z.number(),
  statement: z.string(), // source up to `:=` (theorems) / capped full source (defs)
  sorry_free: z.boolean(),
  axioms: z.array(z.string()).nullable(), // null = not checked (v1)
  /** Composite objects (no standalone decl): the Lean pieces that jointly
   *  formalize the statement — component decls and/or theorem hypothesis binders. */
  components: z.array(z.object({ label: z.string(), statement: z.string() })).optional(),
});
export type LeanSnippet = z.infer<typeof LeanSnippet>;

export const LeanSnippets = z.object({
  commit: z.string(),
  snippets: z.record(z.string(), LeanSnippet), // key = obj_id
});
export type LeanSnippets = z.infer<typeof LeanSnippets>;

/** Web-only "Formal layer" panel: every from-note object with its NL + Lean + verified status,
 *  generated deterministically from the graph (no LLM). A complete backstop guaranteeing every
 *  object is reachable even if an inline \leanref is missed. */
export const FormalLayerItem = z.object({
  obj_id: z.string(),
  kind: z.string(),
  label: z.string(), // e.g. "Assumption A-3"
  nl: z.string(), // the verified NL statement
  lean: CrosswalkLean.nullable(),
  status: z.string(), // causalsmith review status
  sorry_free: z.boolean().nullable(),
});
export type FormalLayerItem = z.infer<typeof FormalLayerItem>;

export const FormalLayer = z.object({
  commit: z.string(),
  groups: z.array(z.object({ kind: z.string(), items: z.array(FormalLayerItem) })),
});
export type FormalLayer = z.infer<typeof FormalLayer>;

export const PaperMeta = z.object({
  qid: z.string(),
  spec: z.string(),
  title: z.string(),
  tldr: z.string().default(""), // 1-2 sentence skim summary; abstract folds under it on the site
  abstract: z.string(),
  area: z.string(),
  authorship: z.string().nullable(), // user decides per paper; null until then
  created: z.string(),
  wp_number: z.string().nullable(),
  // P5 referee's holistic overall score (0–10, one decimal) + one-line rationale.
  // Injected by P5 (after P4 emits meta); advisory — gates nothing. Drives the
  // site's "self-reported score" badge and best-first ordering. null = unreviewed.
  score: z.number().nullable().default(null),
  score_rationale: z.string().nullable().default(null),
});
export type PaperMeta = z.infer<typeof PaperMeta>;
