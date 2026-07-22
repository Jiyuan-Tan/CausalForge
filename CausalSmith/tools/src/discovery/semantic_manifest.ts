import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import { z } from "zod";
import { artifactPath } from "../paths.js";
import type { PipelineContext } from "../types.js";
import type { Core, CoreStatement } from "./core/schema.js";
import type { WorkingState } from "./stages/d0_working.js";

const LayerSchema = z.enum(["proto", "core", "working", "solve"]);
const StatementContractSchema = z.object({
  id: z.string().min(1),
  scopes: z.array(LayerSchema).min(1),
  exact_depends_on: z.array(z.string()).optional(),
  statement_includes: z.array(z.string()).default([]),
  proof_includes: z.array(z.string()).default([]),
});
const ForbiddenSchema = z.object({ id: z.string().min(1), scopes: z.array(LayerSchema).min(1) });
const ResolvedOeqSchema = z.object({ source_id: z.string().min(1), theorem_id: z.string().min(1) });

export const SemanticManifestSchema = z.object({
  version: z.literal(1),
  statements: z.array(StatementContractSchema).default([]),
  forbidden_statements: z.array(ForbiddenSchema).default([]),
  resolved_oeqs: z.array(ResolvedOeqSchema).default([]),
  render: z.object({
    required_literals: z.array(z.string()).default([]),
    forbidden_literals: z.array(z.string()).default([]),
  }).optional(),
});

export type SemanticManifest = z.infer<typeof SemanticManifestSchema>;
type Layer = z.infer<typeof LayerSchema>;

export function semanticManifestPath(ctx: PipelineContext): string {
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", "semantic_manifest.json", [
    `${ctx.qid}_semantic_manifest.json`,
  ]);
}

export async function loadSemanticManifest(ctx: PipelineContext): Promise<SemanticManifest | null> {
  const p = semanticManifestPath(ctx);
  if (!existsSync(p)) return null;
  return SemanticManifestSchema.parse(JSON.parse(await readFile(p, "utf8")));
}

function assertStatement(layer: Layer, stmt: CoreStatement, contract: z.infer<typeof StatementContractSchema>): void {
  if (contract.exact_depends_on) {
    const actual = stmt.depends_on ?? [];
    if (JSON.stringify(actual) !== JSON.stringify(contract.exact_depends_on)) {
      throw new Error(
        `Stage 0 semantic manifest ${layer}: ${stmt.id} depends_on=${JSON.stringify(actual)}; ` +
          `expected exactly ${JSON.stringify(contract.exact_depends_on)}`,
      );
    }
  }
  for (const literal of contract.statement_includes) {
    if (!stmt.statement.includes(literal)) {
      throw new Error(`Stage 0 semantic manifest ${layer}: ${stmt.id} statement is missing literal ${JSON.stringify(literal)}`);
    }
  }
  const proof = stmt.proof_tex ?? "";
  for (const literal of contract.proof_includes) {
    if (!proof.includes(literal)) {
      throw new Error(`Stage 0 semantic manifest ${layer}: ${stmt.id} proof is missing literal ${JSON.stringify(literal)}`);
    }
  }
}

export function validateCoreManifest(
  manifest: SemanticManifest | null,
  layer: "proto" | "core",
  core: Core,
): void {
  if (!manifest) return;
  const byId = new Map(core.statements.map((s) => [s.id, s] as const));
  for (const forbidden of manifest.forbidden_statements.filter((x) => x.scopes.includes(layer))) {
    if (byId.has(forbidden.id)) throw new Error(`Stage 0 semantic manifest ${layer}: forbidden statement ${forbidden.id} is present`);
  }
  for (const contract of manifest.statements.filter((x) => x.scopes.includes(layer))) {
    const stmt = byId.get(contract.id);
    if (!stmt) throw new Error(`Stage 0 semantic manifest ${layer}: required statement ${contract.id} is absent`);
    assertStatement(layer, stmt, contract);
  }
}

export function validateWorkingManifest(manifest: SemanticManifest | null, working: WorkingState): void {
  if (!manifest) return;
  for (const forbidden of manifest.forbidden_statements.filter((x) => x.scopes.includes("working"))) {
    if (working.solved[forbidden.id]) throw new Error(`Stage 0 semantic manifest working: forbidden statement ${forbidden.id} is present`);
  }
  for (const contract of manifest.statements.filter((x) => x.scopes.includes("working"))) {
    const rec = working.solved[contract.id];
    if (!rec) throw new Error(`Stage 0 semantic manifest working: required statement ${contract.id} is absent`);
    const node = rec.node;
    const depends_on = node?.depends_on ?? rec.snapshot.depends_on ?? [];
    const statement = node?.statement ?? rec.snapshot.stmt;
    assertStatement("working", {
      id: contract.id,
      kind: node?.kind ?? "lemma",
      statement,
      depends_on,
      status: node?.status ?? "proved",
      proof_tex: rec.proof_tex,
    } as CoreStatement, contract);
  }
  for (const expected of manifest.resolved_oeqs) {
    const raw = working.resolved_oeqs?.[expected.source_id];
    const theoremId = typeof raw === "string" ? raw : raw?.theorem_id;
    if (theoremId !== expected.theorem_id) {
      throw new Error(
        `Stage 0 semantic manifest working: ${expected.source_id} resolves to ${theoremId ?? "<absent>"}; ` +
          `expected ${expected.theorem_id}`,
      );
    }
  }
}

function emittedStatements(output: unknown): CoreStatement[] {
  if (!output || typeof output !== "object") return [];
  const o = output as Record<string, unknown>;
  const added = Array.isArray(o.added_lemmas) ? o.added_lemmas : [];
  const resolved = Array.isArray(o.resolved_oeqs)
    ? o.resolved_oeqs.map((r) => (r && typeof r === "object" ? (r as Record<string, unknown>).theorem : null))
    : [];
  return [...added, ...resolved].filter((x): x is CoreStatement => !!x && typeof x === "object" && "id" in x);
}

export function validateSolveManifest(manifest: SemanticManifest | null, outputs: unknown[]): void {
  if (!manifest) return;
  const emitted = outputs.flatMap(emittedStatements);
  const proofRecords = outputs.flatMap((output) => {
    if (!output || typeof output !== "object") return [];
    const proofs = (output as Record<string, unknown>).proofs;
    return Array.isArray(proofs) ? proofs : [];
  }).filter((x): x is { id: string; proof_tex?: string } => !!x && typeof x === "object" && "id" in x);
  const emittedById = new Map(emitted.map((s) => [s.id, s] as const));
  const proofById = new Map(proofRecords.map((p) => [p.id, p.proof_tex ?? ""] as const));
  for (const forbidden of manifest.forbidden_statements.filter((x) => x.scopes.includes("solve"))) {
    if (emittedById.has(forbidden.id) || proofById.has(forbidden.id)) {
      throw new Error(`Stage 0 semantic manifest solve: forbidden statement ${forbidden.id} was emitted`);
    }
  }
  for (const contract of manifest.statements.filter((x) => x.scopes.includes("solve"))) {
    const stmt = emittedById.get(contract.id);
    if (stmt) assertStatement("solve", stmt, contract);
    const proof = proofById.get(contract.id);
    if (proof !== undefined) {
      for (const literal of contract.proof_includes) {
        if (!proof.includes(literal)) {
          throw new Error(`Stage 0 semantic manifest solve: ${contract.id} proof is missing literal ${JSON.stringify(literal)}`);
        }
      }
    }
  }
}

export function validateRenderedManifest(manifest: SemanticManifest | null, tex: string): void {
  if (!manifest?.render) return;
  for (const literal of manifest.render.required_literals) {
    if (!tex.includes(literal)) throw new Error(`Stage 0 semantic manifest render: missing literal ${JSON.stringify(literal)}`);
  }
  for (const literal of manifest.render.forbidden_literals) {
    if (tex.includes(literal)) throw new Error(`Stage 0 semantic manifest render: forbidden literal ${JSON.stringify(literal)} is present`);
  }
}
