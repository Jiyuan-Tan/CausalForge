import { readFile, writeFile, appendFile, mkdir } from "node:fs/promises";
import { MODELS } from "../../models.js";
import { join } from "node:path";
import type { StageIO } from "../pipeline.js";
import { presentationPrompt } from "../prompt_io.js";
import { parseOutline } from "../stage_util.js";
import { lintAnchors, lintDefinitionOrder, hashEnvBody, normalizeFrozenEnvs, parseAnchoredEnvs, repairObjRefs } from "../tex_anchors.js";
import { FormalLayerSource, normalizeCitedScopeFootnotes } from "../formal_layer.js";
import { parseBib } from "../citations.js";
import { savePaperState } from "../state.js";
import { writeJsonAtomic } from "../json_io.js";
import { repairLatexStringsDeep } from "../../discovery/core/latex_serialization.js";
import {
  runHardGates,
  gateLoop,
  minRubric,
  parseRubricReview,
  parseJsonLoose,
  type GateRunners,
  type HardGateInput,
  type RubricReview,
} from "../gates.js";

const MAX_ROUNDS = 2;
const RUBRIC_PASS = 6;

/** The frozen presentation env names (must match FormalBlock.env). */
const FROZEN_ENV_NAMES = [
  "theoremv",
  "assumptionv",
  "lemmav",
  "definitionv",
  "citedv",
  "propositionv",
  "remarkv",
] as const;

/**
 * Remove the frozen statement envs from a stretch of section text, leaving the
 * surrounding interpretive PROSE. The overclaim gate audits prose against the
 * frozen claims (supplied separately as `frozenEnvsTex`), so it must NOT see the
 * frozen claims inside the prose too: a frozen env sits in the Discussion/etc.
 * section, and if the gate flags a phrase INSIDE it the reviser cannot fix it
 * (editing a frozen body trips the frozen-layer guard and aborts the round). A
 * frozen statement is the fidelity-gated proved claim itself — not prose that can
 * over- or under-claim — so stripping it here is correct, not a workaround.
 */
function stripFrozenEnvs(tex: string): string {
  let out = tex;
  for (const env of FROZEN_ENV_NAMES) {
    out = out.replace(new RegExp(`\\\\begin\\{${env}\\}[\\s\\S]*?\\\\end\\{${env}\\}`, "g"), "");
  }
  return out;
}

/** Remove full-line LaTeX comments before model-facing prose audits. These lines are
 * not reader-visible claims; provenance markers such as `% DERIVED ...` must not
 * consume a P3 revision round as alleged overclaiming. */
export function stripLatexCommentLines(tex: string): string {
  return tex.replace(/^[ \t]*%.*(?:\r?\n|$)/gm, "");
}

/** Stable prose units for differential overclaim re-review. */
export function claimUnits(tex: string): string[] {
  return tex
    .replace(/\s+/g, " ")
    .split(/(?<=[.!?])\s+(?=(?:\\|[A-Z]))/)
    .map((s) => s.trim())
    .filter((s) => /[A-Za-z]/.test(s));
}

function contextualClaimUnits(tex: string): { sentence: string; context: string; ordinal: number }[] {
  const units = claimUnits(tex);
  return units.map((sentence, i) => ({
    sentence,
    ordinal: i,
    context: [units[i - 1] ?? "(start)", sentence, units[i + 1] ?? "(end)"].join("\n"),
  }));
}

export interface TextReplacement { before: string; after: string }

const FROZEN_ENV_BLOCK_RE = new RegExp(
  `\\\\begin\\{(?:${FROZEN_ENV_NAMES.join("|")})\\}[\\s\\S]*?\\\\end\\{(?:${FROZEN_ENV_NAMES.join("|")})\\}`,
  "g",
);

/** Keep a misbehaving revision model from routing frozen statement bodies through
 * exact replacement. Only prose before the first and after the last frozen block
 * can be recovered unambiguously; canonical statement bodies are restored later. */
export function proseOnlyReplacements(replacements: TextReplacement[]): TextReplacement[] {
  return replacements.flatMap(({ before, after }) => {
    const beforeBlocks = [...before.matchAll(FROZEN_ENV_BLOCK_RE)];
    const afterBlocks = [...after.matchAll(FROZEN_ENV_BLOCK_RE)];
    if (beforeBlocks.length === 0 && afterBlocks.length === 0) return [{ before, after }];

    const beforeFirst = beforeBlocks[0]?.index ?? before.length;
    const afterFirst = afterBlocks[0]?.index ?? after.length;
    const beforeLast = beforeBlocks.at(-1);
    const afterLast = afterBlocks.at(-1);
    const beforeTail = beforeLast ? before.slice(beforeLast.index! + beforeLast[0].length) : "";
    const afterTail = afterLast ? after.slice(afterLast.index! + afterLast[0].length) : "";
    const edges = [
      { before: before.slice(0, beforeFirst), after: after.slice(0, afterFirst) },
      { before: beforeTail, after: afterTail },
    ];
    return edges.filter((r) => r.before.length > 0 && r.before !== r.after);
  });
}

/** Apply exact, unique replacements only; ambiguity is a hard failure. */
export function applyTargetedReplacements(tex: string, replacements: TextReplacement[]): string {
  let out = tex;
  for (const { before, after } of replacements) {
    if (!before || before === after) continue;
    const first = out.indexOf(before);
    if (first < 0 || out.indexOf(before, first + before.length) >= 0) {
      throw new Error(`P3 patch replacement is missing or non-unique: ${before.slice(0, 100)}`);
    }
    out = out.slice(0, first) + after + out.slice(first + before.length);
  }
  return out;
}

/** Select the paragraphs most lexically related to the reported problems. */
export function revisionContext(tex: string, details: string[]): string {
  const terms = new Set(details.join(" ").toLowerCase().match(/[a-z][a-z0-9_-]{3,}/g) ?? []);
  const parts = tex.split(/\n\s*\n/);
  const scored = parts.map((part, i) => ({
    part,
    i,
    score: (part.toLowerCase().match(/[a-z][a-z0-9_-]{3,}/g) ?? []).filter((t) => terms.has(t)).length,
  }));
  const selected = scored
    .filter((x) => x.score > 0)
    .sort((a, b) => b.score - a.score || a.i - b.i)
    .slice(0, 10)
    .sort((a, b) => a.i - b.i)
    .map((x) => x.part);
  return (selected.length > 0 ? selected : parts.slice(0, 6)).join("\n\n");
}

const PROOF_BLOCK_RE = /\\begin\{proof\}(?:\[[^\]]*\])?[\s\S]*?\\end\{proof\}/g;

function proofBlocks(tex: string): string[] {
  // AUDIT-R3: P3 does not re-run proof audits, so proof block edits must be detected locally.
  return [...tex.matchAll(PROOF_BLOCK_RE)].map((m) => m[0]);
}

/** Restore P2-audited proof blocks while preserving P3's prose edits. A changed proof-block count
 * is structural and cannot be paired safely, so return null and let the caller hard-stop. */
export function restoreAuditedProofBlocks(tex: string, audited: string[]): string | null {
  const current = proofBlocks(tex);
  if (current.length !== audited.length) return null;
  let i = 0;
  return tex.replace(PROOF_BLOCK_RE, () => audited[i++]);
}

/**
 * P3 — WHOLE-PAPER hard gates (overclaiming, citation pool + support, anchor lint) with a bounded
 * revise loop, then the soft rubric ensemble. The Lean-anchored PER-ARTIFACT audits now run with the
 * stage that produces the artifact: statement equivalence at P1 (runStatementAudit), proof
 * faithfulness at P2 (runProofAudit) — so a failure surfaces at its source rather than being
 * re-discovered here. Codex runs the overclaim gate; opus provides the independent prose review via
 * half the rubric ensemble (opus ×1 + codex ×1), so the prose is scored by a model that did not write
 * it. The statement/proof runners remain on the `runners` object only to satisfy the shared
 * `GateRunners` contract for `runHardGates` (which audits no proofs here — `proofs: []`).
 */
export async function stageP3(io: StageIO): Promise<void> {
  await mkdir(io.outDir, { recursive: true });
  if (io.ctx.deps.dryRun) {
    await writeFile(join(io.outDir, "p3.stub"), "dry-run\n");
    return;
  }
  const { deps } = io.ctx;
  // `state.revision_round` is a pipeline-wide counter: P5 increments it when a
  // healing pass starts, and prior P3 invocations may already have revised the
  // paper.  P3's two-round budget is per invocation, so never use that durable
  // counter as the local gate-loop cursor.
  let p3RevisionRound = 0;
  /**
   * Persist state, THEN throw.
   *
   * `pipeline.ts` only calls `savePaperState` after a stage returns, so a stage that
   * records a diagnosis and then throws loses it: `hard_gate_failures` was assigned at
   * all three failure exits below and still read `[]` in every run on disk, even when
   * `run_p3.log` showed the equivalence gate failing on 7 statements. The record is
   * the whole point of the field — write it before unwinding.
   */
  const failP3 = async (message: string): Promise<never> => {
    await savePaperState(io.outDir, io.state).catch(() => {}); // never mask the real error
    throw new Error(message);
  };
  const paperPath = join(io.outDir, "paper.tex");
  const reviewsPath = join(io.outDir, "reviews.jsonl");
  const formalLayer = FormalLayerSource.parse(
    JSON.parse(await readFile(join(io.outDir, "formal_layer.json"), "utf8")),
  );
  const frozen = new Map<string, string>(formalLayer.blocks.map((b) => [b.obj_id, b.body_hash]));
  const notation = parseOutline(await readFile(join(io.outDir, "outline.md"), "utf8")).notation;
  const frozenEnvsTex = await readFile(join(io.outDir, "formal_layer.tex"), "utf8");
  const canonicalFrozen = new Map(
    parseAnchoredEnvs(frozenEnvsTex).map((e) => [
      e.obj_id,
      `\\begin{${e.env}}{${e.obj_id}}${e.title ? `[${e.title}]` : ""}\n${e.body.trim()}\n\\end{${e.env}}`,
    ]),
  );
  const bibEntries = parseBib(await readFile(join(io.outDir, "references.bib"), "utf8"));
  const brief = await readFile(join(io.outDir, "related_work_brief.md"), "utf8").catch(() => "");
  // P3 protects the complete P1 formal-layer namespace, including presentation-owned setup
  // definitions that intentionally have no bank crosswalk/Lean declaration.
  const known = new Set(frozen.keys());

  // Definition order is structural: P3 prose revision cannot move or rewrite the P1-frozen
  // environments. Fail directly with a P1 repair instruction instead of burning revision rounds.
  const definitionOrderProblems = lintDefinitionOrder(await readFile(paperPath, "utf8"), notation);
  if (definitionOrderProblems.length > 0) {
    io.state.hard_gate_failures = definitionOrderProblems;
    await failP3(
      `P3 definition-order gate failed (${definitionOrderProblems.map((p) => p.detail).join("; ")}). ` +
        `Repair the P1 notation/home ordering; do not restart the presentation run.`,
    );
  }

  // Per-gate verdict cache, content-keyed: P3 is the expensive stage, so a
  // rerun must only re-pay for inputs that actually changed. Same input →
  // same cached verdict (including failures — delete gate_cache.json to
  // force a fresh audit).
  const gateCachePath = join(io.outDir, "gate_cache.json");
  interface GateCache {
    citationSupport: Record<string, { verdict: string; reason?: string }>;
    overclaim: Record<string, { clean: boolean; flags?: { sentence: string; fix?: string }[] }>;
    overclaimUnits: Record<string, { flag: { sentence: string; fix?: string } | null }>;
    rubric: Record<string, RubricReview[]>;
  }
  const gateCache: GateCache = {
    citationSupport: {},
    overclaim: {},
    overclaimUnits: {},
    rubric: {},
    ...JSON.parse(await readFile(gateCachePath, "utf8").catch(() => "{}")),
  };
  // Legacy cache values can carry decoded control-escape corruption (lost \to /
  // \ref in quoted TeX) from before the escape defense; repair on read. Keys are
  // input-content hashes, so repairing values never invalidates the cache.
  repairLatexStringsDeep(gateCache);
  // Atomic: citation-support workers save concurrently under mapLimit, and a plain
  // writeFile racing/crashing mid-write corrupts the cache (next P3 run throws on
  // parse until the operator deletes it and re-pays every cached verdict).
  const saveGateCache = () => writeJsonAtomic(gateCachePath, gateCache);

  const ask = async (out: Promise<string> | Promise<{ stdout: string; stderr: string }>) => {
    const res = await out;
    return parseJsonLoose(typeof res === "string" ? res : res.stdout);
  };

  const runners: GateRunners = {
    equivalence: async () => {
      throw new Error("P3 equivalence runner is retired; statement audits run at P1"); // why: buildInput passes no statements.
    },
    proofAudit: async () => {
      throw new Error("P3 proof audit runner is retired; proof audits run at P2"); // why: buildInput passes proofs: [].
    },
    proofAuditBatch: async () => new Map(), // why: retained only to satisfy the shared GateRunners shape.
    overclaim: async (frontMatter, envsTex) => {
      const auditFrontMatter = stripLatexCommentLines(frontMatter);
      const auditEnvsTex = stripLatexCommentLines(envsTex);
      const envKey = hashEnvBody(auditEnvsTex);
      const units = contextualClaimUnits(auditFrontMatter);
      const flags: { sentence: string; fix?: string }[] = [];
      const misses: { id: number; sentence: string; context: string; key: string }[] = [];
      units.forEach(({ sentence, context, ordinal }, id) => {
        // Key on the sentence + its neighbour context, NOT the absolute `ordinal`:
        // with the ordinal in the key, inserting or deleting a single sentence
        // invalidates every later sentence and forces a whole-document re-audit
        // (measured: 6 such full re-audits in one run at ~75-80k chars each).
        void ordinal;
        const key = hashEnvBody(`${sentence}|${context}|${envKey}`);
        const hit = gateCache.overclaimUnits[key];
        if (hit) {
          if (hit.flag) flags.push(hit.flag);
        } else misses.push({ id: id + 1, sentence, context, key });
      });
      if (misses.length === 0) return { clean: flags.length === 0, flags };
      const v = (await ask(
        deps.runCodex({ multiAgent: false, // P3 gates fan out ×GATE_CONCURRENCY — keep codex sub-agents off (concurrent multi-agent deadlocks the daemon)
          prompt: await presentationPrompt("p3_overclaim", {
            front_matter_tex: misses
              .map((m) => `[CLAIM ${m.id}]\nNeighbor context:\n${m.context}\nSentence to classify:\n${m.sentence}`)
              .join("\n\n"),
            frozen_envs: auditEnvsTex,
          }),
          cwd: io.ctx.repoRoot,
          reasoningEffort: "medium",
          leanLsp: false,
        }),
      )) as { clean?: boolean; flags?: { id?: number; sentence: string; fix?: string }[] } | null;
      if (!v || typeof v.clean !== "boolean" || !Array.isArray(v.flags)) {
        return {
          clean: false,
          flags: [{ sentence: misses[0].sentence, fix: "Overclaim auditor returned invalid JSON; re-run the gate." }],
        };
      }
      let matchedFlags = 0;
      const pending: { key: string; flag: { sentence: string; fix?: string } | null }[] = [];
      for (const miss of misses) {
        const flagged = v.flags.find((f) =>
          f.id === miss.id || f.sentence.replace(/^\[CLAIM \d+\]\s*/, "").trim() === miss.sentence,
        );
        const flag = flagged ? { sentence: miss.sentence, fix: flagged.fix } : null;
        if (flagged) matchedFlags += 1;
        pending.push({ key: miss.key, flag });
        if (flag) flags.push(flag);
      }
      // Only commit to cache once we know the response was usable. Caching inside the
      // loop above poisoned the cache when the auditor reported an overclaim we could
      // not match: every unit was stored `flag: null`, so the "re-run the gate" retry
      // then hit an all-clean cache and the gate passed vacuously with zero model calls.
      if (v.clean || matchedFlags > 0) {
        for (const p of pending) gateCache.overclaimUnits[p.key] = { flag: p.flag };
      }
      if (!v.clean && matchedFlags === 0) {
        return {
          clean: false,
          flags: [{ sentence: misses[0].sentence, fix: "Auditor reported an unmatched overclaim; re-run the gate." }],
        };
      }
      const out = { clean: flags.length === 0, flags };
      await saveGateCache();
      return out;
    },
    citationSupportBatch: async (pairs) => {
      // Cost economy: ~10 (sentence, citation) pairs per low-effort codex call;
      // verdicts cached per pair, misses fall through to individual calls.
      const out = new Map<
        string,
        { verdict: "supported" | "unsupported" | "unverifiable"; reason?: string }
      >();
      const citationKey = (p: typeof pairs[number]) =>
        hashEnvBody([
          p.sentence,
          p.entry.key,
          p.entry.fields.title ?? "",
          p.entry.fields.author ?? "",
          p.entry.fields.year ?? "",
          p.entry.fields.abstract ?? p.entry.fields.note ?? "",
          hashEnvBody(brief),
        ].join("§")); // why: citation prompt depends on bib metadata and related-work context.
      const misses: typeof pairs = [];
      for (const p of pairs) {
        const key = citationKey(p);
        const hit = gateCache.citationSupport[key];
        if (hit) out.set(`${p.entry.key}|${p.sentence}`, hit as never);
        else misses.push(p);
      }
      const CBATCH = 10;
      for (let i = 0; i < misses.length; i += CBATCH) {
        const group = misses.slice(i, i + CBATCH);
        if (group.length < 2) break; // singles go through the individual path
        const items = group
          .map(
            (p, j) =>
              `[${j + 1}] sentence: ${p.sentence}\n    cited work (${p.entry.key}): ${p.entry.fields.title ?? ""} — ${p.entry.fields.author ?? ""} (${p.entry.fields.year ?? ""})\n    abstract/notes: ${(p.entry.fields.abstract ?? p.entry.fields.note ?? "").slice(0, 600)}`,
          )
          .join("\n\n");
        try {
          const parsed = (await ask(
            deps.runCodex({ multiAgent: false, // P3 gates fan out ×GATE_CONCURRENCY — keep codex sub-agents off (concurrent multi-agent deadlocks the daemon)
              prompt: await presentationPrompt("p3_citation_support_batch", {
                items_block: items,
                related_work_brief: brief,
              }),
              cwd: io.ctx.repoRoot,
              reasoningEffort: "low",
              leanLsp: false,
            }),
          )) as { results?: { id?: number; verdict?: string; reason?: string }[] } | null;
          for (const r of parsed?.results ?? []) {
            const p = typeof r.id === "number" ? group[r.id - 1] : undefined;
            if (!p) continue;
            if (r.verdict === "supported" || r.verdict === "unsupported" || r.verdict === "unverifiable") {
              const v: { verdict: "supported" | "unsupported" | "unverifiable"; reason?: string } = {
                verdict: r.verdict,
                reason: r.reason,
              };
              out.set(`${p.entry.key}|${p.sentence}`, v);
              gateCache.citationSupport[citationKey(p)] = v;
            }
          }
        } catch {
          /* group falls through to individual calls */
        }
      }
      // Persist before returning: without this the batch verdicts live only in
      // memory, so a later hard-gate throw loses the whole batch and the next
      // round re-pays byte-identical calls (measured: 90 wasted calls in one run).
      if (misses.length > 0) await saveGateCache();
      return out;
    },
    citationSupport: async (sentence, entry) => {
      // codex at low effort (user decision 2026-06-10: prefer codex credit for
      // high-volume cheap gates). Swap `model` for a cheaper codex id here once
      // one is verified against this CLI.
      const key = hashEnvBody([
        sentence,
        entry.key,
        entry.fields.title ?? "",
        entry.fields.author ?? "",
        entry.fields.year ?? "",
        entry.fields.abstract ?? entry.fields.note ?? "",
        hashEnvBody(brief),
      ].join("§")); // why: citation prompt inputs extend beyond sentence and bib key.
      const hit = gateCache.citationSupport[key];
      if (hit) return hit as { verdict: "supported" | "unsupported" | "unverifiable"; reason?: string };
      const v = (await ask(
        deps.runCodex({ multiAgent: false, // P3 gates fan out ×GATE_CONCURRENCY — keep codex sub-agents off (concurrent multi-agent deadlocks the daemon)
          prompt: await presentationPrompt("p3_citation_support", {
            sentence,
            bib_key: entry.key,
            bib_title: entry.fields.title ?? "",
            bib_authors: entry.fields.author ?? "",
            bib_year: entry.fields.year ?? "",
            bib_abstract: entry.fields.abstract ?? entry.fields.note ?? "",
            related_work_brief: brief,
          }),
          cwd: io.ctx.repoRoot,
          reasoningEffort: "low",
          leanLsp: false,
        }),
      )) as { verdict?: string; supported?: boolean; reason?: string } | null;
      const verdict: "supported" | "unsupported" | "unverifiable" =
        v?.verdict === "supported" || v?.verdict === "unsupported" || v?.verdict === "unverifiable"
          ? v.verdict
          : v?.supported === true // legacy boolean shape
            ? "supported"
            : "unverifiable";
      const out = { verdict, reason: v?.reason ?? "unparseable auditor output" };
      gateCache.citationSupport[key] = out;
      await saveGateCache();
      return out;
    },
  };

  const buildInput = async (): Promise<HardGateInput> => {
    let paperTex = await readFile(paperPath, "utf8");
    const refRepair = repairObjRefs(paperTex, new Set(parseAnchoredEnvs(paperTex).map((e) => e.obj_id)));
    if (refRepair.tex !== paperTex) {
      // why: P3 applies unique obj-ref repairs before lint/audit — BUT a `\ref` inside a FROZEN env
      // body must never be rewritten (that persists frozen-drift the lint would reject). Only write the
      // repair if it leaves every anchored env body byte-identical; otherwise skip and let the
      // downstream ref lint surface it (pre-fix behavior) rather than corrupting a frozen statement.
      const beforeBodies = new Map(parseAnchoredEnvs(paperTex).map((e) => [e.obj_id, hashEnvBody(e.body)]));
      const frozenTouched = parseAnchoredEnvs(refRepair.tex).some(
        (e) => beforeBodies.has(e.obj_id) && beforeBodies.get(e.obj_id) !== hashEnvBody(e.body),
      );
      if (!frozenTouched) {
        paperTex = refRepair.tex;
        await writeFile(paperPath, paperTex, "utf8");
      }
    }
    // Proof faithfulness is audited at P2 (runProofAudit), co-located with proof production, so the P3
    // hard gates no longer re-audit proofs (proofs: []). P3's runHardGates covers anchor lint, cite
    // pool, overclaim, and citation support.
    const proofs: HardGateInput["proofs"] = [];
    const abstract = paperTex.match(/\\begin\{abstract\}[\s\S]*?\\end\{abstract\}/)?.[0] ?? "";
    const intro = paperTex.match(/\\section\{Introduction\}[\s\S]*?(?=\\section\{)/)?.[0] ?? "";
    // Interpretive body sections carry the comparative / qualitative claims
    // (monotonicity, phase behavior, "free lunch") the overclaim gate must see —
    // the abstract/intro can be correct while a discussion aside contradicts the
    // proved rate. Include discussion/conclusion/extensions/interpretation.
    const interpretive = [
      ...paperTex.matchAll(
        /\\section\{[^}]*(?:Discussion|Conclusion|Extensions?|Interpretation)[^}]*\}[\s\S]*?(?=\\section\{|\\appendix|\\end\{document\}|$)/g,
      ),
    ]
      .map((m) => m[0])
      .join("\n\n");
    // Strip frozen envs from the prose the overclaim gate audits: it compares
    // interpretive prose against the frozen claims (passed separately as
    // `frozenEnvsTex`), and a frozen env flagged inside the prose is unfixable by
    // the reviser (it would trip the frozen-layer guard and abort the round).
    const frontMatter = stripFrozenEnvs(`${abstract}\n\n${intro}\n\n${interpretive}`);
    const input: HardGateInput = {
      paperTex,
      notation,
      knownObjIds: known,
      frozenHashes: frozen,
      proofs,
      frontMatter,
      frozenEnvsTex,
      bibEntries,
    };
    return input;
  };

  // NOTE: statement equivalence (vs Lean) now runs at P1 (runStatementAudit) and proof equivalence
  // at P2 (runProofAudit) — each co-located with the stage that produces the artifact. P3 keeps only
  // the WHOLE-PAPER gates below (overclaim, citation pool + support, anchor lint, rubric).

  // Revision is a bounded exact-replacement patch over only the relevant prose
  // paragraphs. The model never receives or rewrites the full paper.
  const revise = async (problems: { gate: string; detail: string }[], round: number) => {
    const before = await readFile(paperPath, "utf8");
    const beforeProofs = proofBlocks(before);
    // P3 cannot edit frozen statement environments. Do not show them to the
    // prose reviser, and omit rubric requests whose only proposed action is to
    // delete or rewrite synthesized definitions.
    const proseProblems = problems.filter(
      (p) => !/Definitions?\s+(?:~?\\(?:Cref|cref|ref)\{obj:)?synth[_:{0-9-]/i.test(p.detail),
    );
    if (proseProblems.length === 0) {
      throw new Error(`P3 revision round ${round} has no prose-repairable findings`);
    }
    const { stdout } = await deps.runCodex({
      multiAgent: false, // P3
      prompt: await presentationPrompt("p3_revision_patch", {
        problems: proseProblems.map((p) => `- [${p.gate}] ${p.detail}`).join("\n"),
        paper_excerpt: revisionContext(stripFrozenEnvs(before), proseProblems.map((p) => p.detail)),
      }),
      cwd: io.ctx.repoRoot,
      reasoningEffort: "high",
      leanLsp: false,
    });
    const parsed = parseJsonLoose(stdout) as { replacements?: TextReplacement[] } | null;
    if (!parsed?.replacements?.length) throw new Error(`P3 revision round ${round} returned no replacements`);
    const agentRevision = applyTargetedReplacements(before, proseOnlyReplacements(parsed.replacements));
    const proofRestored = restoreAuditedProofBlocks(agentRevision, beforeProofs);
    if (proofRestored === null) {
      await writeFile(paperPath, before, "utf8");
      throw new Error(
        "P3 revision round " + round +
          " changed the proof-block count (restored); rerun the proof-audited stage before publishing",
      );
    }
    // The revision model owns prose, never the P1-frozen formal layer. Re-impose each canonical
    // environment mechanically before proof/integrity checks so an incidental paraphrase cannot
    // turn a repairable prose round into a terminal halt. Do this before the no-change check: when
    // P1 was re-audited after a Lean move, canonical resynchronization may be the only required edit
    // and the prose agent is correct to leave the frozen block alone. Missing/extra envs still fail.
    const revised = normalizeCitedScopeFootnotes(
      normalizeFrozenEnvs(proofRestored, canonicalFrozen),
      formalLayer.blocks,
    );
    await writeFile(paperPath, revised, "utf8");
    if (revised === before) {
      throw new Error(`P3 revision round ${round} made no changes to paper.tex`);
    }
    const afterProofs = proofBlocks(revised);
    if (JSON.stringify(afterProofs) !== JSON.stringify(beforeProofs)) {
      await writeFile(paperPath, before, "utf8");
      // why: P3 revises whole paper.tex without proof audit inputs; proof edits require a P2 re-audit.
      throw new Error(`P3 revision round ${round} changed proof blocks (restored); rerun the proof-audited stage before publishing`);
    }
    const lint = [...lintAnchors(revised, known, frozen), ...lintDefinitionOrder(revised, notation)];
    if (lint.length > 0) {
      await writeFile(paperPath, before, "utf8");
      throw new Error(
        `P3 revision round ${round} broke the frozen layer (restored): ${lint.map((p) => p.detail).join("; ")}`,
      );
    }
    p3RevisionRound = round;
    io.state.revision_round += 1;
  };

  // "citation-unverifiable" is advisory (evidence silent, nothing
  // contradicts): logged for the record, never a hard failure and never fed
  // to revision (it is unfixable by prose edits and would burn rounds).
  const isAdvisory = (p: { gate: string }) => p.gate === "citation-unverifiable";

  const result = await gateLoop({
    maxRounds: MAX_ROUNDS,
    run: async () => {
      const problems = await runHardGates(await buildInput(), runners);
      await appendFile(
        reviewsPath,
        JSON.stringify({ kind: "hard-gates", round: p3RevisionRound, problems }) + "\n",
        "utf8",
      );
      const advisories = problems.filter(isAdvisory);
      if (advisories.length > 0) {
        io.state.notes.push(
          `P3: ${advisories.length} citation-support advisories (unverifiable, not failures) — see reviews.jsonl`,
        );
      }
      return problems.filter((p) => !isAdvisory(p));
    },
    revise,
  });
  if (!result.ok) {
    io.state.hard_gate_failures = result.problems;
    await failP3(
      `P3 hard gates still failing after ${result.rounds} revision rounds: ` +
        result.problems.map((p) => `[${p.gate}] ${p.detail}`).join("; "),
    );
  }

  // soft rubric ensemble: opus ×1 + codex ×1 (user decision 2026-06-10: the
  // two opus reviews scored near-identically, so the duplicate bought nothing;
  // pass = MIN of the two means, keeping the harsher reviewer binding), cached
  // on the paper content.
  // Scored as a function so the rubric can be RE-SCORED after a revision: without a
  // re-score the threshold is unenforceable (runs shipped at min 4.75/5.0/5.5/5.75).
  // Re-reading paper.tex each time also makes the content-keyed cache do the right
  // thing — an unchanged manuscript re-scores for free, a revised one really re-scores.
  const scoreRubric = async (): Promise<{ reviews: RubricReview[]; minScore: number }> => {
    const paperTex = await readFile(paperPath, "utf8");
    const rubricMode = io.ctx.p3ReviewMode ?? "final";
    const rubricKey = hashEnvBody(`${rubricMode}|${paperTex}`);
    // Cache reads bypass the reviewer dispatch, so they must be re-validated: a
    // cache written by pre-fix code can hold string-scored reviews whose mean is
    // NaN (NaN < RUBRIC_PASS is false → silent fail-open). Filter every array
    // read from the cache through parseRubricReview, dropping invalid entries.
    const validReviews = (vs: unknown[] | undefined): RubricReview[] =>
      (vs ?? []).map((v) => parseRubricReview(v)).filter((v): v is RubricReview => v !== null);
    let reviews: RubricReview[];
    const cached = validReviews(gateCache.rubric[rubricKey]);
    if (cached.length > 0) {
      reviews = cached;
    } else {
      const rubricPrompt = await presentationPrompt("p3_rubric", { paper_tex: paperTex });
      const intermediateKey = hashEnvBody(`intermediate|${paperTex}`);
      reviews = rubricMode === "final" ? validReviews(gateCache.rubric[intermediateKey]) : [];
      const rubricRuns = reviews.length > 0
        ? [() => deps.runCodex({ prompt: rubricPrompt, cwd: io.ctx.repoRoot, reasoningEffort: "medium" as const, leanLsp: false, multiAgent: false })]
        : [
            () => deps.runClaude({ prompt: rubricPrompt, model: MODELS.claudeMain, cwd: io.ctx.repoRoot }),
            ...(rubricMode === "final"
              ? [() => deps.runCodex({ prompt: rubricPrompt, cwd: io.ctx.repoRoot, reasoningEffort: "medium" as const, leanLsp: false, multiAgent: false })]
              : []),
          ];
      for (const run of rubricRuns) {
        const v = parseRubricReview(await ask(run()));
        if (v) reviews.push(v);
      }
      if (reviews.length === 0) {
        throw new Error("P3 rubric: no reviewer returned a valid review (scores must be finite numbers) — re-run P3");
      }
      gateCache.rubric[rubricKey] = reviews;
      await saveGateCache();
    }
    await appendFile(reviewsPath, JSON.stringify({ kind: "rubric", reviews }) + "\n", "utf8");
    return { reviews, minScore: minRubric(reviews) };
  };

  let { reviews, minScore } = await scoreRubric();
  if (minScore < RUBRIC_PASS && p3RevisionRound < MAX_ROUNDS) {
    await revise(
      reviews.flatMap((r) => r.weaknesses).map((w) => ({ gate: "rubric", detail: w })),
      p3RevisionRound + 1,
    );
    // A broad prose-quality revision can accidentally add an unsupported citation or restore an
    // overclaim even though frozen statements/proofs remain protected. Close that loop with the
    // same bounded hard-gate reviser instead of halting on a repairable regression.
    const repairStart = p3RevisionRound;
    const repair = await gateLoop({
      maxRounds: Math.max(0, MAX_ROUNDS - repairStart),
      run: async () =>
        (await runHardGates(await buildInput(), runners)).filter((p) => !isAdvisory(p)),
      revise: (problems, localRound) => revise(problems, repairStart + localRound),
    });
    if (!repair.ok) {
      io.state.hard_gate_failures = repair.problems;
      await failP3(
        `P3: rubric revision left hard-gate failures after ${repair.rounds} repair round(s): ` +
          repair.problems.map((p) => `[${p.gate}] ${p.detail}`).join("; "),
      );
    }
    ({ reviews, minScore } = await scoreRubric());
  }
  // Enforce the threshold. Previously `RUBRIC_PASS` was only a trigger for one revision
  // pass and never a stage outcome, so a manuscript that stayed below it shipped anyway.
  // The residual score is recorded either way so a pass near the line is still visible.
  io.state.notes.push(`P3: rubric min score ${minScore.toFixed(2)} (pass = ${RUBRIC_PASS}).`);
  if (minScore < RUBRIC_PASS) {
    const weaknesses = [...new Set(reviews.flatMap((r) => r.weaknesses))];
    await failP3(
      `P3: rubric min score ${minScore.toFixed(2)} is below the ${RUBRIC_PASS} pass threshold after ` +
        `${p3RevisionRound < MAX_ROUNDS ? "a revision pass" : "the revision-round cap"}. ` +
        `Remaining weaknesses: ${weaknesses.map((w) => `• ${w}`).join(" ")}`,
    );
  }
}
