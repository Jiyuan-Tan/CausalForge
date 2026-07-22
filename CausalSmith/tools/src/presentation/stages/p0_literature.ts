import { writeFile, mkdir } from "node:fs/promises";
import { join } from "node:path";
import type { StageIO } from "../pipeline.js";
import { presentationPrompt } from "../prompt_io.js";
import { extractFenced, bibChunks } from "../stage_util.js";
import { parseBib, verifyEntry, defaultLookup } from "../citations.js";
import { MODELS } from "../../models.js";

/** Strip LaTeX comment lines — the Stage -1 skeleton is mostly `%` scaffolding
 * addressed to the pipeline ("HOW TO USE THIS FILE"), which is pure prompt noise. */
const stripTexComments = (tex: string) =>
  tex.split("\n").filter((l) => !/^\s*%/.test(l)).join("\n").replace(/\n{3,}/g, "\n\n").trim();

/** An unfilled Stage -1 proposal skeleton: `% TODO(stage-1 …)` markers still present. */
const isSkeleton = (tex: string) => /TODO\(stage-1/.test(tex);

/**
 * P0's stated anchor-literature source is `discovery/proposal.tex`, but in every banked
 * entry to date that file is the UNFILLED Stage -1 skeleton (14 `% TODO(stage-1 …)`
 * markers, zero prose) — so P0 has been running with an empty primary input while the
 * real derivation sits next to it as `discovery/writeup.tex`. Prefer a substantive
 * proposal, fall back to the derivation, and fail loud if neither is usable rather than
 * silently building the citation pool from the topic string alone.
 */
function anchorLiterature(io: StageIO): string {
  const proposal = (io.bank.proposalTex ?? "").trim();
  if (proposal && !isSkeleton(proposal)) return stripTexComments(proposal);
  const derivation = (io.bank.derivationTex ?? "").trim();
  if (!derivation) {
    throw new Error(
      "P0: no anchor literature available — discovery/proposal.tex is missing or is an unfilled " +
        "Stage -1 skeleton, and discovery/writeup.tex is absent. Building a citation pool from the " +
        "topic string alone would produce an unsourced bibliography.",
    );
  }
  io.state.notes.push(
    proposal
      ? "P0: discovery/proposal.tex is an unfilled Stage -1 skeleton; used discovery/writeup.tex as the anchor-literature source."
      : "P0: discovery/proposal.tex absent; used discovery/writeup.tex as the anchor-literature source.",
  );
  return stripTexComments(derivation);
}

/**
 * P0 — literature refresh. Builds the verified citation pool BEFORE any
 * drafting: codex (with its hosted web_search tool) extracts + searches, then
 * every entry is verified against an external record; `major` failures are
 * dropped from the pool, `minor` ones kept with a note.
 */
export async function stageP0(io: StageIO): Promise<void> {
  await mkdir(io.outDir, { recursive: true });
  if (io.ctx.deps.dryRun) {
    await writeFile(join(io.outDir, "p0.stub"), "dry-run\n");
    return;
  }
  const prompt = await presentationPrompt("p0_literature", {
    topic: io.bank.readme.topic ?? io.ctx.qid,
    proposal_tex: anchorLiterature(io),
    source_bibliography: JSON.stringify(io.bank.sourceBibliography, null, 2),
    // The full reviews jsonl is too large to inline; the proposal already
    // carries the anchor-literature map, which is what P0 needs.
    novelty_review: "",
  });
  // Codex with its hosted web_search tool (server-side search + open_page) builds
  // the pool; the sandbox stays network-off. High effort — search + extraction +
  // faithful bibtex. (Stage -1.1 already uses codex web_search the same way.)
  const { stdout: out } = await io.ctx.deps.runCodex({
    prompt,
    cwd: io.ctx.repoRoot,
    reasoningEffort: "high",
    leanLsp: false,
    // Pin P0 to the same presentation tier explicitly so its model choice is
    // visible in the per-run transcript rather than hidden in CLI injection.
    model: MODELS.codexPresentation,
  });
  const bib = extractFenced(out, "bibtex");
  const brief = extractFenced(out, "markdown");
  if (!bib || !brief) throw new Error("P0 output missing the bibtex/markdown fenced blocks");
  // Raw pre-verification pool, so drops are auditable after the fact.
  await writeFile(join(io.outDir, "references_raw.bib"), bib + "\n", "utf8");

  const lookup = io.ctx.deps.lookup ?? defaultLookup;
  const chunks = bibChunks(bib);
  const kept: string[] = [];
  const report: { key: string; verdict: string; detail: string }[] = [];
  for (const entry of parseBib(bib)) {
    const v = await verifyEntry(entry, lookup);
    report.push(v);
    if (v.verdict === "major") {
      io.state.notes.push(`P0: dropped unverifiable bib entry ${entry.key}: ${v.detail}`);
      continue;
    }
    if (v.verdict === "minor") {
      io.state.notes.push(`P0: kept ${entry.key} with metadata caveat: ${v.detail}`);
    }
    const chunk = chunks.get(entry.key);
    if (chunk) kept.push(chunk);
  }
  await writeFile(
    join(io.outDir, "p0_verification.json"),
    JSON.stringify(report, null, 2) + "\n",
    "utf8",
  );
  const dropped = report.filter((r) => r.verdict === "major").length;
  if (kept.length === 0) throw new Error("P0: citation pool empty after verification");
  if (dropped / report.length > 0.4) {
    throw new Error(
      `P0: ${dropped}/${report.length} bib entries failed verification — that rate suggests a lookup defect, not hallucination. See p0_verification.json and references_raw.bib.`,
    );
  }
  await writeFile(join(io.outDir, "references.bib"), kept.join("\n\n") + "\n", "utf8");
  await writeFile(join(io.outDir, "related_work_brief.md"), brief + "\n", "utf8");
}
