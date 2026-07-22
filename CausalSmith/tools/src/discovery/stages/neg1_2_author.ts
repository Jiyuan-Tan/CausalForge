// Stage -1.2 author (single artifact) — the WHOLE D-1.2 producer in one dispatch.
//
// One agent authors the typed proposal core: formal fields (symbols, pure-condition
// assumptions, class/construction definitions, to-prove statements) AND prose fields
// (tldr, project_justification gap→niche→fill, related_work, per-statement
// justification/gap/consumer). The core is the single source of truth AND the sole
// artifact: discovery consumers (the D-0.5 reviewer, D0-CORE) read the proto_core JSON
// directly, so NO proposal .tex is rendered here (the D0 derivation .tex — F3 roadmap —
// is rendered later by D0-RENDER). Flow: dispatch → write core.json → proposal gate
// (G1–G7 + GP1/GP2/GP3) → schema-validate. The author's stdout JSON (seeds /
// literature_map / cluster / novelty_justification / literature_checklist) is returned
// as `handoff` for the -0.5 loop. See D0_CORE_REDESIGN.md §12.
import { existsSync } from "node:fs";
import { mkdir, readFile } from "node:fs/promises";
import path from "node:path";
import { MODEL_PLAN } from "../../constants.js";
import { artifactPath } from "../../paths.js";
import { discoveryBrief, parseStageOutput, readPrompt, type StageDeps } from "../../pipeline_support.js";
import { extractJsonObject } from "../../judgment.js";
import type { PipelineContext, StateJson } from "../../types.js";
import { CoreSchema } from "../core/schema.js";
import {
  assertNoDecodedControlChars,
  normalizeRawModelJson,
  repairCoreLatexSerialization,
} from "../core/latex_serialization.js";
import { runGates } from "../framework/gates.js";
import { dispatchAgent } from "../../framework/agent_dispatch.js";
import { proposalGate } from "../framework/gate_registrations.js";
import { writeJsonAtomic } from "../../shared/json_atomic.js";

/** Filesystem path for `<qid>_proto_core.json` (the D-1-authored proposal core). */
export function protoCoreJsonPath(ctx: PipelineContext): string {
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", "proto_core.json", [`${ctx.qid}_proto_core.json`]);
}

/** The five producer modes; each maps to `stage_neg1_2_proto_head_<mode>.txt`. */
export type Neg1_2Mode = "cold-start" | "revise" | "pivot" | "kernel-replace" | "draft-rebuild";

export interface StageNeg1_2ProtoCoreResult {
  /** `needs-pivot` = the author could not author this mode (revise can't fix in
   * place / no surviving seed); the dual producer records it on proposed_from so
   * the -0.5 orchestrator drives the pivot. No core is written in that case. */
  status: "completed" | "needs-pivot";
  message: string;
  protoCoreJsonPath: string;
  /** The author's stdout receipt merged with ideation metadata from the validated
   * proto core. The core is authoritative because the final stdout contract is a
   * deliberately small status receipt and may omit seeds / literature metadata. */
  handoff: Record<string, unknown>;
}

/** Ideation-metadata keys preserved verbatim from the raw authored core at the
 * persist boundary (everything else outside CoreSchema is dropped — see the
 * persist comment in `runStageNeg1_2ProtoCore`). Exported so the prompt↔schema
 * contract test can prove every prompt-mandated field survives persistence. */
export const CORE_HANDOFF_KEYS = [
  "seeds",
  "seed_details",
  "literature_map",
  "cluster",
  "novelty_justification",
  "literature_checklist",
] as const;

/** Preserve the small stdout status receipt while sourcing proposal metadata
 * from the single validated artifact. This prevents an emitted-to-persisted
 * drop when the model follows the final minimal stdout instruction exactly. */
function mergeCoreHandoff(
  core: Record<string, unknown>,
  stdoutHandoff: Record<string, unknown>,
): Record<string, unknown> {
  const merged = { ...stdoutHandoff };
  for (const key of CORE_HANDOFF_KEYS) {
    if (Object.prototype.hasOwnProperty.call(core, key)) merged[key] = core[key];
  }
  return merged;
}

/**
 * Build the MODE-SPECIFIC input block: the prior core to edit (revise /
 * kernel-replace / draft-rebuild), the surviving seed list (pivot), and the prior
 * reviewer verdict (every non-cold-start mode). Cold-start has none. The prior
 * core is read from `corePath` BEFORE the author overwrites it.
 */
async function modeInputBlock(mode: Neg1_2Mode, state: StateJson, corePath: string): Promise<string> {
  const pf = state.proposed_from;
  const blocks: string[] = [];
  const editsPrior = mode === "revise" || mode === "kernel-replace" || mode === "draft-rebuild";
  if (editsPrior && existsSync(corePath)) {
    blocks.push(
      "=== PRIOR PROPOSAL CORE (edit in place — re-emit the FULL revised core to this same path) ===",
      await readFile(corePath, "utf8"),
      "=== END PRIOR PROPOSAL CORE ===",
    );
  }
  if (mode === "pivot") {
    blocks.push(
      "=== PIVOT CONTEXT (the prior cursor is exhausted — obey any explicit carry-forward directive before choosing a new seed) ===",
      `seed_list: ${JSON.stringify(pf?.seed_list ?? [])}`,
      `exhausted_angles: ${JSON.stringify(pf?.exhausted_angles ?? [])}`,
      "=== END PIVOT CONTEXT ===",
    );
  }
  if (mode !== "cold-start" && typeof pf?.last_reviewer_verdict === "string" && pf.last_reviewer_verdict.length > 0) {
    blocks.push(
      "=== PRIOR REVIEWER VERDICT (load-bearing — address the flagged items) ===",
      pf.last_reviewer_verdict,
      "=== END PRIOR REVIEWER VERDICT ===",
    );
  }
  return blocks.join("\n");
}

export async function runStageNeg1_2ProtoCore(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  /** Producer mode — selects the head prompt + the mode-specific input block. */
  mode: Neg1_2Mode;
  /** Optional extra prompt blocks (D-1.1 gaps / motif library / flagship directive)
   * assembled by the caller; appended to the prompt. Mode-specific inputs (prior
   * core / seeds / reviewer verdict) are assembled HERE, not by the caller. */
  contextBlocks?: string;
}): Promise<StageNeg1_2ProtoCoreResult> {
  const corePath = protoCoreJsonPath(args.ctx);
  await mkdir(path.dirname(corePath), { recursive: true });

  const headName = `stage_neg1_2_proto_head_${args.mode.replace(/-/g, "_")}.txt`;
  const modeBlock = await modeInputBlock(args.mode, args.state, corePath);

  const basePrompt = [
    await readPrompt(args.ctx, headName),
    "",
    await readPrompt(args.ctx, "stage_neg1_2_proto_core.txt"),
    "",
    discoveryBrief(args.ctx, args.state),
    args.contextBlocks ? `\n${args.contextBlocks}` : "",
    modeBlock ? `\n${modeBlock}` : "",
    "",
    `Write the typed proposal core JSON to this path (create it): ${corePath}`,
    'Return only JSON on stdout: {"status":"completed"|"needs-pivot","message":"...","artifacts":["<proto_core.json>"], "literature_checklist":[...]}.',
  ].join("\n");

  // The proposal gate (G1–G7 + GP1–GP3) can reject the authored core (e.g. prose
  // in an atomic `condition`/target field). Re-author with the violations fed back
  // — bounded by a small budget — instead of aborting the whole run on the first
  // miss (this is the "fix and re-author" path the gate throw-site names).
  const REAUTHOR_BUDGET = 3;
  let lastGateFeedback = "";

  for (let attempt = 1; attempt <= REAUTHOR_BUDGET; attempt++) {
    const prompt = lastGateFeedback
      ? `${basePrompt}\n\n── PRIOR ATTEMPT REJECTED BY THE PROPOSAL GATE ──\n` +
        `Your previous core failed these structural checks:\n${lastGateFeedback}\n` +
        `Fix EXACTLY these and re-author the COMPLETE corrected core JSON. Atomic ` +
        `fields (an assumption \`condition\`, formal target/objective expressions) must ` +
        `hold ONLY formal symbolic content — move any explanatory prose into the ` +
        `designated prose/description fields.`
      : basePrompt;

    const out = await dispatchAgent({
      ctx: args.ctx,
      deps: args.deps,
      stage: "-1.2",
      label: `D-1.2 proto-core author (mode=${args.mode}, attempt ${attempt}/${REAUTHOR_BUDGET})`,
      prompt,
      promptSources: [
        `prompts/D-1/${headName}`,
        "prompts/D-1/stage_neg1_2_proto_core.txt",
        ...(args.contextBlocks ? ["caller-context-blocks"] : []),
        ...(modeBlock ? ["mode-input-block"] : []),
        ...(lastGateFeedback ? ["gate-feedback"] : []),
      ],
      model: MODEL_PLAN.mechanicalTier.model,
      reasoningEffort: MODEL_PLAN.mechanicalTier.effort,
      inactivityTimeoutMs: 40 * 60 * 1000,
    });
    const parsedOut = parseStageOutput(out.stdout);
    if (parsedOut.status === "parse_failed") {
      // AUDIT-A: fail closed on unparseable stage output; why: Stage -1.2 must not advance on garbage.
      throw new Error("Stage -1.2: proto-core author output did not parse (parse_failed) - refusing to advance on unparseable output");
    }
    if (parsedOut.status === "failed") {
      throw new Error(
        `Stage -1.2 author reported status "failed": ${parsedOut.message ?? "(no message)"} — ` +
          `the proposal is not authorable as posed; pivot or revise the angle.`,
      );
    }
    // needs-pivot: the author declined this mode (revise can't fix in place / no
    // surviving seed). Not an error — the -0.5 orchestrator drives the pivot.
    // The author may still have written a diagnostic proto core containing the
    // cold-start seed slate. Harvest those ideation fields before returning;
    // otherwise every pivot receives an empty seed_list and mechanically burns
    // the proposal budget. The diagnostic core is intentionally not proposal-
    // gate/schema validated because it is not advancing as an authored proposal.
    if (parsedOut.status === "needs-pivot") {
      let handoff: Record<string, unknown> = {};
      try {
        handoff = extractJsonObject(out.stdout) as Record<string, unknown>;
      } catch {
        /* best-effort */
      }
      if (existsSync(corePath)) {
        try {
          const diagnosticCore = JSON.parse(normalizeRawModelJson(await readFile(corePath, "utf8"))) as Record<string, unknown>;
          handoff = mergeCoreHandoff(diagnosticCore, handoff);
        } catch {
          /* best-effort: the stdout receipt still drives needs-pivot */
        }
      }
      return {
        status: "needs-pivot",
        message: parsedOut.message ?? "Stage -1.2 author returned needs-pivot",
        protoCoreJsonPath: corePath,
        handoff,
      };
    }
    if (!existsSync(corePath)) {
      if (attempt === REAUTHOR_BUDGET) {
        throw new Error(`Stage -1.2 author completed without writing the required core at ${corePath}`);
      }
      lastGateFeedback = `  [WRITE] ${corePath}: author completed without writing the core file`;
      continue;
    }

    let core: unknown;
    try {
      // Pre-parse raw-byte normalization: repair under-escaped TeX backslashes
      // while the raw bytes still distinguish them from intended control escapes.
      core = JSON.parse(normalizeRawModelJson(await readFile(corePath, "utf8")));
    } catch (e) {
      if (attempt === REAUTHOR_BUDGET) {
        throw new Error(`Stage -1.2 author wrote a core at ${corePath} that is not valid JSON: ${String(e)}`);
      }
      lastGateFeedback = `  [JSON] ${corePath}: not valid JSON (${String(e)})`;
      continue;
    }

    // Proposal gate: G1–G7 + GP1 (tag content) + GP2 (nothing proven) + GP3 (prose
    // fields present). One call — the prose lives in the core, so there is no second
    // artifact and no \coreref coverage to check.
    const gateViolations = runGates([proposalGate], core).hard;
    if (gateViolations.length > 0) {
      lastGateFeedback = gateViolations.map((v) => `  ${v.detail}`).join("\n");
      if (attempt === REAUTHOR_BUDGET) {
        throw new Error(
          `Stage -1.2 author fails the proposal gate after ${REAUTHOR_BUDGET} attempts — last violations:\n${lastGateFeedback}`,
        );
      }
      continue;
    }

    // Schema-validate and canonicalize at the producer boundary. Leaving decoded
    // JSON control escapes in proto_core makes every later exact-echo comparison
    // disagree with a solver that correctly re-emits the intended LaTeX.
    // No .tex is rendered: the proto_core JSON is the sole discovery artifact.
    const typedCore = CoreSchema.parse(core);
    repairCoreLatexSerialization(typedCore);
    // Backstop: any control character surviving normalization + repair is an
    // escaping error the model must fix; feed it back as a re-author round
    // instead of persisting silently corrupted TeX.
    try {
      assertNoDecodedControlChars(typedCore, "Stage -1.2 proposal core");
    } catch (e) {
      if (attempt === REAUTHOR_BUDGET) throw e;
      lastGateFeedback = `  [ESCAPE] ${e instanceof Error ? e.message : String(e)}`;
      continue;
    }
    CoreSchema.parse(typedCore);
    // Persist the canonicalized core plus ONLY the allowlisted ideation keys
    // (seeds, seed_details, literature_map, ...): CoreSchema strips unknown keys,
    // and both the cold-start harvest below and post-interrupt rehydration read
    // those keys from this object / the persisted file. A blanket raw-core spread
    // would let the author persist arbitrary non-schema keys that later flow
    // verbatim into the D-0.5 reviewer prompt (audit finding: prompt injection /
    // payload bloat), so everything outside the allowlist is dropped here.
    const rawCore = core as Record<string, unknown>;
    const persistedCore: Record<string, unknown> = { ...typedCore };
    for (const key of CORE_HANDOFF_KEYS) {
      if (Object.prototype.hasOwnProperty.call(rawCore, key)) persistedCore[key] = rawCore[key];
    }
    // Emitted-vs-persisted visibility: the drop above is intentional, but it must
    // never be SILENT — a prompt-mandated field missing from CoreSchema/allowlist
    // otherwise vanishes here and is only discovered rounds later as a reviewer
    // <MISSING> (the comparator_promise_table incident).
    const droppedKeys = Object.keys(rawCore).filter(
      (key) => !Object.prototype.hasOwnProperty.call(persistedCore, key),
    );
    if (droppedKeys.length > 0) {
      console.warn(
        `[D-1.2] persist boundary dropped non-schema key(s) from the authored core: ` +
          `${droppedKeys.join(", ")} — if the prompt mandates one of these, give it a home in ` +
          `CoreSchema or CORE_HANDOFF_KEYS (contract: prompt_schema_contract.test.ts)`,
      );
    }
    await writeJsonAtomic(corePath, persistedCore);
    core = persistedCore;

    let stdoutHandoff: Record<string, unknown> = {};
    try {
      stdoutHandoff = extractJsonObject(out.stdout) as Record<string, unknown>;
    } catch {
      /* gate already passed; harvest is best-effort */
    }

    const handoff = mergeCoreHandoff(core as Record<string, unknown>, stdoutHandoff);

    return {
      status: "completed",
      message: parsedOut.message ?? "Stage -1.2 authored the proposal core",
      protoCoreJsonPath: corePath,
      handoff,
    };
  }

  // Unreachable: every iteration returns or throws (the budget-th attempt throws).
  throw new Error("Stage -1.2 author re-author loop exhausted without resolution");
}
