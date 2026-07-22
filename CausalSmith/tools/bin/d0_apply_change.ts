#!/usr/bin/env -S npx tsx
/**
 * Orchestrator helper for the D0-SOLVE escalation loop.
 *
 * When D0-SOLVE checkpoints with proposed statement/definition changes, the
 * orchestrator reviews them and applies the accepted ones to the frozen proto.
 * This CLI does that atomically AND records an escalation-log entry, so the next
 * D0 round reuses unchanged proofs and the re-solving agent sees what was changed
 * and why. Stale round outputs are cleared; the incremental working state is KEPT.
 *
 * Every D0 proposal checkpoints before mutation. This CLI is the explicit,
 * auditable path for applying the ids the orchestrator accepted.
 *
 * Usage:
 *   npx tsx tools/bin/d0_apply_change.ts <qid> <spec> [--ids id1,id2 | --id <id> ... | --all] [--note "..."] [--check]
 *   (--id is repeatable and comma-safe; required for LaTeX symbol ids containing commas)
 *
 * SELECTORS may be kind-qualified. A bare id selects that node in every proposal
 * channel, which is what you usually want; but one round can propose BOTH a claim
 * change and a typed core edit on the SAME node, and those are independent decisions.
 * Prefix the id to accept one and reject the other:
 *
 *   thm:x                      every proposal touching thm:x (default, unchanged)
 *   statement:thm:x            only the claim-text change
 *   core-edit:thm:x            only the typed core edit(s)
 *   statement-replace:thm:x    only that one core-edit kind
 *
 * Accepted qualifiers are the four channels (statement, definition, assumption,
 * core-edit) and any core-edit kind (statement-replace, bibliography-replace, …).
 */
import { existsSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import { fileURLToPath } from "node:url";
import { applyProposedChanges, parseProposalSelectors, validateProposalSelectors } from "../src/discovery/stages/d0_apply.js";
import type { PipelineContext } from "../src/types.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";


export async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const idsIdx = args.indexOf("--ids");
  // Guard the lookahead: `--ids --all` used to consume `--all` as an id, silently
  // producing a one-element id set that matches nothing.
  const idsRaw = idsIdx !== -1 ? args[idsIdx + 1] : undefined;
  if (idsIdx !== -1 && (idsRaw === undefined || idsRaw.startsWith("--"))) {
    console.error("d0_apply_change: --ids requires a comma-separated id list (got a flag or nothing).");
    process.exitCode = 1;
    return;
  }
  const commaIds = idsIdx !== -1 ? (idsRaw ?? "").split(",").map((s) => s.trim()).filter(Boolean) : [];
  if (idsIdx !== -1) args.splice(idsIdx, 2);
  // `--id` is REPEATABLE and comma-free, mirroring `--require-core-target`. Proposal
  // ids include symbol targets whose names are LaTeX and may themselves contain a
  // comma — e.g. `sym:\(\bar{\mathcal C}_{n,\alpha}^d\)` — which comma-joined `--ids`
  // splits into two unmatchable fragments. Such a target is unaddressable without this.
  const repeatedIds: string[] = [];
  for (;;) {
    const i = args.indexOf("--id");
    if (i === -1) break;
    const value = args[i + 1];
    if (value === undefined || value.startsWith("--")) {
      console.error("d0_apply_change: --id requires a single id value (got a flag or nothing).");
      process.exitCode = 1;
      return;
    }
    repeatedIds.push(value.trim());
    args.splice(i, 2);
  }
  const allIds = [...commaIds, ...repeatedIds];
  const doubleQualified = validateProposalSelectors(allIds);
  if (doubleQualified.length > 0) {
    console.error(
      `d0_apply_change: ${doubleQualified.length} selector(s) carry two kind qualifiers and can never match: ` +
        `${doubleQualified.join(", ")}. Use one qualifier, e.g. statement:thm:x — nothing was mutated.`,
    );
    process.exitCode = 1;
    return;
  }
  // Build the selector ONCE and hand the same instance to both applyProposedChanges
  // passes: it accumulates which selectors matched, which is what names a typo below.
  const ids = allIds.length > 0 ? parseProposalSelectors(allIds) : null;
  const noteIdx = args.indexOf("--note");
  const note = noteIdx !== -1 ? args[noteIdx + 1] : undefined;
  if (noteIdx !== -1) args.splice(noteIdx, 2);
  const all = args.indexOf("--all");
  if (all !== -1) args.splice(all, 1);
  const checkOnly = args.indexOf("--check");
  if (checkOnly !== -1) args.splice(checkOnly, 1);
  // REFUSE UNKNOWN FLAGS. Every recognized flag is spliced out above, so anything
  // `--`-prefixed still here was silently ignored — and for THIS command that is not a
  // harmless no-op. `--dry-run` is the flag a careful operator reaches for before an
  // irreversible bundle apply; it is not the spelling this CLI uses (`--check` is), so
  // it used to be dropped on the floor and the apply proceeded for real, rewriting the
  // frozen proto and deleting statements while the operator believed they were
  // previewing. The output says "Applied N change(s)" either way, so nothing contradicts
  // the mistaken belief. Fail before mutating anything.
  const unknown = args.filter((a) => a.startsWith("--"));
  if (unknown.length > 0) {
    console.error(
      `d0_apply_change: unrecognized flag(s) ${unknown.join(", ")} — nothing was mutated. ` +
        "Valid flags: --ids id1,id2 | --id <id> (repeatable) | --all | --note \"...\" | --check " +
        "(--check is the preview; there is no --dry-run).",
    );
    process.exitCode = 1;
    return;
  }
  const [qid, spec] = args.filter((a) => !a.startsWith("--"));
  if (!qid || !spec) {
    console.error('Usage: d0_apply_change.ts <qid> <spec> [--ids id1,id2 | --all] [--note "..."]');
    process.exitCode = 1;
    return;
  }
  // `--all` was parsed and then discarded, so a bare invocation left ids=null, which
  // applyProposedChanges treats as "apply everything" — i.e. omitting both flags was
  // silently --all. Applying an entire proposal bundle is never something to do by
  // accident; require the intent explicitly.
  if (ids === null && all === -1) {
    console.error(
      "d0_apply_change: refusing to apply. Pass --ids id1,id2 to apply specific proposals, or --all to apply " +
        "the whole bundle. (Omitting both previously meant --all by accident.)",
    );
    process.exitCode = 1;
    return;
  }
  if (ids !== null && all !== -1) {
    console.error("d0_apply_change: --ids and --all are mutually exclusive.");
    process.exitCode = 1;
    return;
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: false };

  // VALIDATE BEFORE MUTATING. Every rejection below used to be reported AFTER a real
  // apply had already rewound `stage_completed`, rewritten the proto, appended the
  // escalation entry, and run `clearRoundOutputs` — deleting core.json, every
  // proposed_*.json, and the round's solve_*.json. The operator was then told
  // "nothing was mutated", which was false, and the round's outputs were gone.
  // A `checkOnly` pass resolves the same selection in memory and touches no file, so
  // a mistyped id or an inapplicable bundle now costs nothing.
  const preview = await applyProposedChanges({ ctx, ids, note, checkOnly: true });

  // Name the selectors that matched nothing. A typo'd id contributes 0 to both the
  // selected count and the applied count, so the atomicity guard inside
  // applyProposedChanges cannot fire — the operator saw only "none matched / none
  // proposed" and could not tell a mistyped id from a round that genuinely proposed
  // nothing. This asks the SELECTOR what it matched rather than inferring it from the
  // applied entries, so a qualified selector is judged against the channel it names:
  // `core-edit:thm:x` is unmatched when the round proposed only a claim change on
  // thm:x, which reading back a bare changed-entry id could not distinguish.
  if (ids !== null) {
    const unmatched = ids.unmatched();
    if (unmatched.length > 0) {
      console.error(
        `d0_apply_change: ${unmatched.length} selector(s) matched no proposal and were NOT applied: ` +
          `${unmatched.join(", ")}. Check against proposed_*.json — nothing was mutated.`,
      );
      process.exitCode = 1;
      return;
    }
  }
  if (preview.length === 0) {
    console.error("No changes applied (none proposed in this round).");
    process.exitCode = 1;
    return;
  }
  // The selection is valid; now perform it for real (or stop here under --check).
  const changed = checkOnly !== -1
    ? preview
    : await applyProposedChanges({ ctx, ids, note, checkOnly: false });
  console.log(`${checkOnly !== -1 ? "Validated" : "Applied"} ${changed.length} change(s)${checkOnly !== -1 ? " with no mutation" : ` to ${qid} proto + logged escalation`}:`);
  for (const c of changed) console.log(`  - ${c.kind} ${c.id}`);
  if (checkOnly === -1) console.log("Re-run D0 (--stop-after D0) to continue; unchanged proofs will be reused.");
}

if (process.argv[1] !== undefined && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  await main().catch((err: unknown) => {
    console.error(`d0_apply_change: ${err instanceof Error ? err.message : String(err)}`);
    process.exitCode = 1;
  });
}
