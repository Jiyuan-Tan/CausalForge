#!/usr/bin/env -S npx tsx
/** Main-orchestrator source-of-record attestation for an agent-authored cited node. */
import process from "node:process";
import { readFile } from "node:fs/promises";
import type { PipelineContext } from "../src/types.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";
import { CoreSchema } from "../src/discovery/core/schema.js";
import { coreJsonPath } from "../src/discovery/stages/d0_core.js";
import { loadWorkingState, saveWorkingState } from "../src/discovery/stages/d0_working.js";
import { writeJsonAtomic } from "../src/shared/json_atomic.js";
import { readTypedCore } from "../src/discovery/core/core_io.js";
import { resolveUpstreamDecision } from "../src/discovery/core/cited_provenance.js";
import { withRunHeartbeat } from "../src/shared/run_heartbeat.js";

const USAGE =
  "Usage: d0_attest_cited_source.ts <qid> <spec> --id <lem:id> --expect-locator <text> " +
  "--verbatim <source-statement> --note <provenance> " +
  "(--upstream <primary citation> [--upstream-locator <text>] [--upstream-cite <bibkey>] | --upstream-none)";

async function main(): Promise<void> {
  const cli = readArgs(process.argv.slice(2));
  const [qid, spec] = cli.positionals();
  const id = cli.value("--id");
  const locator = cli.value("--expect-locator");
  const verbatim = cli.value("--verbatim");
  const note = cli.value("--note");
  if (!qid || !spec || !id || !locator || !verbatim?.trim() || !note?.trim()) {
    throw new Error(USAGE);
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: true };
  await withRunHeartbeat(repoRoot, qid, spec, async () => {
  const cp = coreJsonPath(ctx);
  const core = await readTypedCore(cp);
  const working = await loadWorkingState(ctx);
  if (!working) throw new Error("missing D0 working state");
  const coreNode = core.statements.find((statement) => statement.id === id);
  const workingNode = working.solved[id]?.node;
  if (!coreNode || !workingNode || coreNode.status !== "cited" || workingNode.status !== "cited") {
    throw new Error(`${id} must be the same durable agent-authored cited node in core and working`);
  }
  // Key-order-INSENSITIVE compare. `coreNode` is zod output (schema key order) while
  // `workingNode` is on-disk order, so a plain JSON.stringify comparison is unequal for
  // every node — it always fell through to the proof-stripped branch, which silently
  // accepted ARBITRARY proof_tex divergence between the two stores. For a `cited` node
  // that field holds the source transcription, i.e. exactly what is being attested.
  const canon = (value: unknown): string =>
    JSON.stringify(value, (_k, v) =>
      v && typeof v === "object" && !Array.isArray(v)
        ? Object.fromEntries(Object.entries(v as Record<string, unknown>).sort(([a], [b]) => a.localeCompare(b)))
        : v);
  // D0.R may sanction presentation-only repairs directly in the published core. Those
  // repairs deliberately need not flow back into the solver cursor (a later full render
  // would erase them), and they do not alter what source is being attested. Compare the
  // claim/source identity while ignoring only proof and presentation prose. Keep every
  // structural field -- statement, status, dependencies, symbols, and source locator --
  // fail-closed. For a one-sided partial attestation, ignore exactly the source fields
  // this CLI writes here, then validate their complete persisted payload below.
  const attestationComparable = (value: typeof coreNode): unknown => {
    const copy = structuredClone(value) as unknown as Record<string, unknown>;
    delete copy.proof_tex;
    delete copy.consumer;
    delete copy.gap;
    delete copy.justification;
    const sourceCopy = copy.source;
    if (sourceCopy && typeof sourceCopy === "object" && !Array.isArray(sourceCopy)) {
      const sourceRecord = { ...(sourceCopy as Record<string, unknown>) };
      if (sourceRecord.verbatim_statement !== undefined) {
        delete sourceRecord.verbatim_statement;
        delete sourceRecord.attestation;
        delete sourceRecord.upstream;
      }
      copy.source = sourceRecord;
    }
    return copy;
  };
  if (canon(attestationComparable(coreNode)) !== canon(attestationComparable(workingNode))) {
    throw new Error(`${id} core/working source identity disagrees; refusing attestation`);
  }
  if (!coreNode.source || !workingNode.source || coreNode.source.locator !== locator || workingNode.source.locator !== locator) {
    throw new Error(`${id} locator mismatch; expected ${locator}`);
  }
  const suppliedVerbatim = verbatim.trim();
  for (const [store, node] of [["core", coreNode], ["working", workingNode]] as const) {
    const effectiveText = node.source?.verbatim_statement?.trim() || node.proof_tex?.trim();
    if (effectiveText && effectiveText !== suppliedVerbatim) {
      throw new Error(
        `${id} ${store} effective cited text disagrees with --verbatim; refusing attestation`,
      );
    }
  }
  // Provenance is decided explicitly: a verbatim match proves the source SAYS this,
  // not that the result is DUE TO this source. See cited_provenance.ts.
  const acknowledgeMarker = cli.value("--acknowledge-marker");
  const requestedUpstream = resolveUpstreamDecision({
    upstream: cli.value("--upstream"),
    upstreamLocator: cli.value("--upstream-locator"),
    upstreamCite: cli.value("--upstream-cite"),
    upstreamNone: cli.bool("--upstream-none"),
    acknowledgeMarker,
    verbatim,
    bibkeys: new Set(core.bibliography.map((entry) => entry.key)),
  });
  // Refuse a genuine OVERWRITE (both stores already attested), but allow RESUME after a
  // partial write. The two stores are written in sequence, so an I/O failure between them
  // leaves exactly one attested; refusing on "either store has it" made that state
  // unrecoverable through this CLI — the tool permanently locked itself out of the run.
  // A one-sided attestation may only be completed with byte-identical text, never edited.
  const existingSource = coreNode.source.verbatim_statement
    ? coreNode.source
    : workingNode.source.verbatim_statement
      ? workingNode.source
      : undefined;
  const existingVerbatim = existingSource?.verbatim_statement;
  if (coreNode.source.verbatim_statement && workingNode.source.verbatim_statement) {
    throw new Error(`${id} already has a verbatim source statement; refusing overwrite`);
  }
  if (existingVerbatim && existingVerbatim !== suppliedVerbatim) {
    throw new Error(
      `${id} is half-attested (one store carries a verbatim statement) and the supplied --verbatim differs from it. ` +
        "Re-run with the exact existing text to complete the partial write, or repair the stores by hand.",
    );
  }
  if (existingSource && (
    existingSource.attestation?.by !== "main" ||
    !existingSource.attestation.note.trim() ||
    !existingSource.attestation.at
  )) {
    throw new Error(
      `${id} has a one-sided verbatim payload that is not an authenticated partial write from this main CLI; ` +
        "refusing to launder it as a recovered attestation",
    );
  }
  if (existingSource && canon(existingSource.upstream) !== canon(requestedUpstream)) {
    throw new Error(
      `${id} is half-attested and the requested upstream provenance differs from the persisted payload`,
    );
  }
  // A marker acknowledgement is a judgement call that overrode a check; it belongs in
  // the durable note, not only in the operator's shell history.
  const attestationNote = acknowledgeMarker?.trim()
    ? `${note.trim()} [marker acknowledged: ${acknowledgeMarker.trim()}]`
    : note.trim();
  const source = existingSource
    ? structuredClone(existingSource)
    : (() => {
        const {
          verbatim_statement: _oldVerbatim,
          attestation: _oldAttestation,
          upstream: _oldUpstream,
          ...baseSource
        } = coreNode.source;
        return {
          ...baseSource,
          verbatim_statement: suppliedVerbatim,
          ...(requestedUpstream ? { upstream: requestedUpstream } : {}),
          attestation: { by: "main" as const, note: attestationNote, at: new Date().toISOString() },
        };
      })();
  // Phase 1 (store consolidation): the working record is the authoritative truth —
  // write the attestation there first. The published core.json is then PATCHED in
  // place on the one attested node, never re-rendered: a full re-render from
  // (proto, working) would silently discard any sanctioned D0.R in-place repairs
  // that live only in the published file (audit F5). The next solve commit's
  // render reproduces the attestation from the working record.
  workingNode.source = { ...source };
  coreNode.source = { ...source };
  CoreSchema.parse(core);
  await saveWorkingState(ctx, working);
  await writeJsonAtomic(cp, core);
  console.log(JSON.stringify({
    id,
    locator,
    verbatimLength: verbatim.trim().length,
    attestedBy: "main",
    upstream: requestedUpstream ?? "none (affirmed original to the cited work)",
  }, null, 2));
  });
}

main().catch((error: unknown) => {
  console.error(`d0_attest_cited_source: ${error instanceof Error ? error.message : String(error)}`);
  process.exitCode = 1;
});
