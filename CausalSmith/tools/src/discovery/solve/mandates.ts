import { createHash } from "node:crypto";
import { z } from "zod";
import type { Core, CoreStatement } from "../core/schema.js";
import { assertSealableLatexPayload } from "../core/latex_serialization.js";
import type { RawCoreEdit } from "../stages/d0_apply.js";
import { coreEditTarget } from "../stages/d0_apply.js";
import { ProposedCoreEditSchema } from "./schemas.js";

export const RequiredCoreEditMandateSchema = z.object({
  mandate_id: z.string().regex(/^d0m:[a-f0-9]{64}$/),
  hash_version: z.union([z.literal(2), z.literal(3)]).optional(),
  /** V3: the exact byte string whose sha256 is the mandate id. Integrity is
   * verified by re-hashing these persisted bytes — never by re-serializing the
   * parsed record, which is the writer/reader canonicalization-drift class. */
  sealed: z.string().optional(),
  edit: ProposedCoreEditSchema,
  proposal_revision: z.string(),
  target_snapshot: z.string(),
});
export type RequiredCoreEditMandate = z.infer<typeof RequiredCoreEditMandateSchema>;

const CurrentRequiredCoreEditMandateCancellationSchema = z.object({
  cancellation_id: z.string().regex(/^d0c:[a-f0-9]{64}$/),
  hash_version: z.union([z.literal(1), z.literal(2)]),
  /** V2: the exact byte string whose sha256 is the cancellation id (see the
   * mandate `sealed` field). V1 rows verify by recomputation instead. */
  sealed: z.string().optional(),
  mandate_id: z.string().regex(/^d0m:[a-f0-9]{64}$/),
  reason: z.string().trim().min(1),
});

const LegacyRequiredCoreEditMandateCancellationSchema = z.object({
  cancellation_id: z.string().regex(/^d0mc:[a-f0-9]{64}$/),
  mandate_id: z.string().regex(/^d0m:[a-f0-9]{64}$/),
  reason: z.string().trim().min(1),
}).transform((legacy) => ({
  ...legacy,
  cancellation_id: legacy.cancellation_id.replace(/^d0mc:/, "d0c:"),
  hash_version: 1 as const,
  sealed: undefined as string | undefined,
}));

/** Read pre-versioning cancellation receipts without rewriting immutable journal
 * history. The legacy and current formats hash the same canonical payload; only
 * the prefix and explicit version marker changed. */
export const RequiredCoreEditMandateCancellationSchema = z.union([
  CurrentRequiredCoreEditMandateCancellationSchema,
  LegacyRequiredCoreEditMandateCancellationSchema,
]);
export type RequiredCoreEditMandateCancellation = z.infer<typeof RequiredCoreEditMandateCancellationSchema>;

type WorkingCatalog = { solved: Record<string, { node?: CoreStatement }> } | null;

/** Semantic operation identity: rationale prose never changes what is applied. */
export function coreEditOperationKey(edit: RawCoreEdit): string {
  const { reason: _reason, ...operation } = edit as RawCoreEdit & { reason?: string };
  return JSON.stringify(operation);
}

function expectedMandateId(args: {
  edit: RawCoreEdit;
  proposalRevision?: string;
  targetSnapshot: string;
  hashVersion?: 2;
}): string {
  const payload = args.hashVersion === 2
    ? {
        // V2 binds the adjudicated rationale as well as the semantic operation.
        edit: args.edit,
        proposal_revision: args.proposalRevision ?? null,
        target_snapshot: args.targetSnapshot,
      }
    : {
        // Mandates emitted before hash-versioning addressed the semantic operation
        // only. Keep that exact byte contract so already-durable directives remain
        // readable after the V2 rollout.
        operation: coreEditOperationKey(args.edit),
        proposal_revision: args.proposalRevision ?? null,
        target_snapshot: args.targetSnapshot,
      };
  const digest = createHash("sha256")
    .update(JSON.stringify(payload))
    .digest("hex");
  return `d0m:${digest}`;
}

function expectedCancellationId(args: { mandateId: string; reason: string }): string {
  const digest = createHash("sha256")
    .update(JSON.stringify({ mandate_id: args.mandateId, reason: args.reason }))
    .digest("hex");
  return `d0c:${digest}`;
}

/** Structural (key-order-insensitive) equality between a parsed sealed payload
 * and the record's semantic fields. Purely a divergence guard: the content
 * address itself is always the hash of the persisted `sealed` bytes. */
function structurallyEqual(a: unknown, b: unknown): boolean {
  if (a === b) return true;
  if (Array.isArray(a) || Array.isArray(b)) {
    return Array.isArray(a) && Array.isArray(b) && a.length === b.length &&
      a.every((item, i) => structurallyEqual(item, b[i]));
  }
  if (a === null || b === null || typeof a !== "object" || typeof b !== "object") return false;
  const aKeys = Object.keys(a).sort();
  const bKeys = Object.keys(b).sort();
  return aKeys.length === bKeys.length && aKeys.every((key, i) =>
    key === bKeys[i] &&
    structurallyEqual((a as Record<string, unknown>)[key], (b as Record<string, unknown>)[key]));
}

function assertSealedRecord(args: {
  label: string;
  id: string;
  prefix: "d0m" | "d0c";
  sealed: string | undefined;
  semantic: unknown;
}): void {
  if (args.sealed === undefined) {
    throw new Error(`${args.label} ${args.id} declares a sealed hash version but carries no sealed bytes`);
  }
  const digest = createHash("sha256").update(args.sealed).digest("hex");
  if (args.id !== `${args.prefix}:${digest}`) {
    throw new Error(`${args.label} id/content mismatch: ${args.id} is not the hash of its sealed bytes`);
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(args.sealed);
  } catch {
    throw new Error(`${args.label} ${args.id} carries unparseable sealed bytes`);
  }
  if (!structurallyEqual(parsed, args.semantic)) {
    throw new Error(
      `${args.label} ${args.id} sealed bytes diverge from the record's semantic fields; ` +
        "the record was edited after sealing",
    );
  }
}

export function makeRequiredCoreEditMandateCancellation(args: {
  mandateId: string;
  reason: string;
}): RequiredCoreEditMandateCancellation {
  const reason = args.reason.trim();
  const sealed = JSON.stringify({ mandate_id: args.mandateId, reason });
  const digest = createHash("sha256").update(sealed).digest("hex");
  return RequiredCoreEditMandateCancellationSchema.parse({
    cancellation_id: `d0c:${digest}`,
    hash_version: 2,
    sealed,
    mandate_id: args.mandateId,
    reason,
  });
}

export function assertMandateCancellationIntegrity(
  cancellation: RequiredCoreEditMandateCancellation,
): void {
  if (cancellation.hash_version === 2) {
    assertSealedRecord({
      label: "D0 mandate cancellation",
      id: cancellation.cancellation_id,
      prefix: "d0c",
      sealed: cancellation.sealed,
      semantic: { mandate_id: cancellation.mandate_id, reason: cancellation.reason },
    });
    return;
  }
  const expected = expectedCancellationId({
    mandateId: cancellation.mandate_id,
    reason: cancellation.reason,
  });
  if (cancellation.cancellation_id !== expected) {
    throw new Error(
      `D0 mandate cancellation id/content mismatch: ${cancellation.cancellation_id} should be ${expected}`,
    );
  }
}

/** Apply auditable cancellations before enforcing the remaining exact mandates.
 * A cancellation must name one outstanding content-addressed mandate exactly; it
 * cannot be used as a wildcard or silently replayed against an already-cleared edit. */
export function resolveRequiredCoreEditMandates(args: {
  mandates: RequiredCoreEditMandate[];
  cancellations: RequiredCoreEditMandateCancellation[];
  core: Core;
  working: WorkingCatalog;
  proposalRevision?: string;
}): RequiredCoreEditMandate[] {
  const candidates: RequiredCoreEditMandate[] = [];
  for (const mandate of args.mandates) {
    assertMandateIntegrity(mandate);
    if (!candidates.some((existing) => existing.mandate_id === mandate.mandate_id)) candidates.push(mandate);
  }
  const cancellationsByMandate = new Map<string, RequiredCoreEditMandateCancellation>();
  for (const cancellation of args.cancellations) {
    assertMandateCancellationIntegrity(cancellation);
    if (!candidates.some((mandate) => mandate.mandate_id === cancellation.mandate_id)) {
      throw new Error(
        `D0 cancellation ${cancellation.cancellation_id} names no outstanding mandate ${cancellation.mandate_id}`,
      );
    }
    const prior = cancellationsByMandate.get(cancellation.mandate_id);
    if (prior && prior.cancellation_id !== cancellation.cancellation_id) {
      throw new Error(`D0 has conflicting cancellations for mandate ${cancellation.mandate_id}`);
    }
    cancellationsByMandate.set(cancellation.mandate_id, cancellation);
  }
  return validateRequiredCoreEditMandates({
    ...args,
    mandates: candidates.filter((mandate) => !cancellationsByMandate.has(mandate.mandate_id)),
  });
}

/** Validate, deduplicate, and reject mutually inconsistent mandate sets. This is
 * shared by live assembly and mechanical recovery so neither path can implement a
 * weaker authority boundary. */
export function validateRequiredCoreEditMandates(args: {
  mandates: RequiredCoreEditMandate[];
  core: Core;
  working: WorkingCatalog;
  proposalRevision?: string;
}): RequiredCoreEditMandate[] {
  const mandates: RequiredCoreEditMandate[] = [];
  for (const mandate of args.mandates) {
    assertMandateBasis({
      mandate,
      core: args.core,
      working: args.working,
      proposalRevision: args.proposalRevision,
    });
    if (!mandates.some((existing) => existing.mandate_id === mandate.mandate_id)) mandates.push(mandate);
  }
  const byTarget = new Map<string, Set<string>>();
  for (const mandate of mandates) {
    const target = coreEditTarget(mandate.edit);
    const operations = byTarget.get(target) ?? new Set<string>();
    // A V2 mandate adjudicates its rationale too. Two authorities that require
    // the same operation for different reasons are not interchangeable records;
    // force an explicit reconciliation instead of letting one proposal clear both.
    operations.add(JSON.stringify(mandate.edit));
    byTarget.set(target, operations);
  }
  const conflicts = [...byTarget].filter(([, operations]) => operations.size > 1).map(([target]) => target);
  if (conflicts.length > 0) {
    throw new Error(`D0 has conflicting required core-edit mandates for ${conflicts.join(", ")}; re-adjudicate them`);
  }
  const deletes = new Map<string, Extract<RawCoreEdit, { kind: "statement-delete" }>>();
  for (const mandate of mandates) {
    if (mandate.edit.kind === "statement-delete") deletes.set(mandate.edit.id, mandate.edit);
  }
  const chained = [...deletes.values()].find((edit) =>
    edit.replacement_id !== undefined && deletes.has(edit.replacement_id));
  if (chained) {
    throw new Error(
      `D0 required delete ${chained.id}->${chained.replacement_id} targets a replacement ` +
      "that is itself mandated for deletion; re-adjudicate the chain to one canonical endpoint",
    );
  }
  return mandates;
}

/** A mandate id is a content address, not a caller-selected label. V3 verifies
 * by re-hashing the persisted `sealed` bytes — no re-serialization anywhere, so
 * writer/reader canonicalization drift is impossible by construction. V1/V2
 * rows predate the sealed field and still verify by recomputation. */
export function assertMandateIntegrity(mandate: RequiredCoreEditMandate): void {
  if (mandate.hash_version === 3) {
    assertSealedRecord({
      label: "D0 required edit mandate",
      id: mandate.mandate_id,
      prefix: "d0m",
      sealed: mandate.sealed,
      semantic: {
        edit: mandate.edit,
        proposal_revision: mandate.proposal_revision,
        target_snapshot: mandate.target_snapshot,
      },
    });
    return;
  }
  const expected = expectedMandateId({
    edit: mandate.edit,
    proposalRevision: mandate.proposal_revision,
    targetSnapshot: mandate.target_snapshot,
    hashVersion: mandate.hash_version,
  });
  if (mandate.mandate_id !== expected) {
    throw new Error(
      `D0 required edit mandate id/content mismatch: ${mandate.mandate_id} should be ${expected}`,
    );
  }
}

function statementSnapshot(statement: CoreStatement | undefined): unknown {
  if (!statement) return null;
  const { proof_tex: _proof, status: _status, ...semantic } = statement;
  return semantic;
}

/** Snapshot only the semantic target the edit was adjudicated against. Proof/status
 * churn during a solve is deliberately excluded. */
export function coreEditTargetSnapshot(core: Core, working: WorkingCatalog, edit: RawCoreEdit): string {
  const target = coreEditTarget(edit);
  let value: unknown;
  if (target.startsWith("thm:") || target.startsWith("lem:") || target.startsWith("prop:") ||
      target.startsWith("conj:") || target.startsWith("oeq:")) {
    const targetValue = statementSnapshot(
      core.statements.find((statement) => statement.id === target) ?? working?.solved[target]?.node,
    );
    const replacementId = edit.kind === "statement-delete" ? edit.replacement_id : undefined;
    value = replacementId === undefined
      ? targetValue
      : {
          target: targetValue,
          replacement: statementSnapshot(
            core.statements.find((statement) => statement.id === replacementId) ??
              working?.solved[replacementId]?.node,
          ),
        };
  } else if (target.startsWith("def:")) {
    value = core.definitions.find((definition) => definition.id === target) ?? null;
  } else if (target.startsWith("ass:")) {
    value = core.assumptions.find((assumption) => assumption.id === target) ?? null;
  } else if (target.startsWith("sym:")) {
    const name = target.slice("sym:".length);
    value = core.symbols.find((symbol) => symbol.name === name) ?? null;
  } else if (target.startsWith("bib:")) {
    const key = target.slice("bib:".length);
    value = core.bibliography.find((entry) => entry.key === key) ?? null;
  } else if (target === "metadata:target-estimand") {
    value = core.target_estimand ?? null;
  } else if (target === "metadata:estimand-functional") {
    value = core.estimand_functional ?? null;
  } else if (target === "metadata:comparator-promise-table") {
    value = core.comparator_promise_table ?? null;
  } else {
    value = target; // idempotent derived-metadata rebuild and future metadata channels.
  }
  return JSON.stringify(value);
}

export function makeRequiredCoreEditMandate(args: {
  core: Core;
  working: WorkingCatalog;
  edit: RawCoreEdit;
  proposalRevision: string;
}): RequiredCoreEditMandate {
  // Hash the schema-canonical payload that will actually be persisted. Zod may
  // supply defaults; hashing the caller's pre-parse object would make a freshly
  // written mandate fail its first integrity read.
  const edit = ProposedCoreEditSchema.parse(args.edit);
  // Validate before immortalizing: a defective payload rejected here is re-emitted
  // cheaply; the same defect sealed into an immutable mandate needs an audited
  // cancellation to undo (the 2026-07-30 over-escaped definition-replace incident).
  assertSealableLatexPayload(edit, `D0 mandate for ${coreEditTarget(edit)}`);
  const targetSnapshot = coreEditTargetSnapshot(args.core, args.working, edit);
  const sealed = JSON.stringify({
    edit,
    proposal_revision: args.proposalRevision,
    target_snapshot: targetSnapshot,
  });
  const digest = createHash("sha256").update(sealed).digest("hex");
  // Derive the record's semantic fields from the sealed bytes rather than the
  // in-memory objects: JSON.stringify drops explicitly-undefined keys, and a
  // record whose fields differ from its own sealed payload would fail integrity
  // before it was ever persisted.
  return RequiredCoreEditMandateSchema.parse({
    mandate_id: `d0m:${digest}`,
    hash_version: 3,
    sealed,
    ...JSON.parse(sealed),
  });
}

export function assertMandateBasis(args: {
  mandate: RequiredCoreEditMandate;
  core: Core;
  working: WorkingCatalog;
  proposalRevision?: string;
}): void {
  assertMandateIntegrity(args.mandate);
  if (args.mandate.proposal_revision !== args.proposalRevision) {
    throw new Error(
      `D0 required edit ${args.mandate.mandate_id} was adjudicated against proposal revision ` +
      `${args.mandate.proposal_revision ?? "unversioned"}, not ${args.proposalRevision ?? "unversioned"}; re-adjudicate it`,
    );
  }
  const live = coreEditTargetSnapshot(args.core, args.working, args.mandate.edit);
  if (live !== args.mandate.target_snapshot) {
    throw new Error(
      `D0 required edit ${args.mandate.mandate_id} target changed since adjudication; refusing stale operation ` +
      `${coreEditTarget(args.mandate.edit)}`,
    );
  }
}
