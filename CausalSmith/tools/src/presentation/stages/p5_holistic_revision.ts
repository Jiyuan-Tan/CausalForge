import { readFile, rm, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { digestPaths, texFilesUnder } from "../assembly_freshness.js";
import { presentationPrompt } from "../prompt_io.js";
import type { StageIO } from "../pipeline.js";
import type { PriorReview } from "../revision_brief.js";
import { findingFingerprint, revisionMode } from "../revision_routing.js";
import { MODELS } from "../../models.js";
import { FormalLayerSource } from "../formal_layer.js";
import { applyProseRevision } from "../prose_revision.js";
import { loadBankNarrative } from "../bank.js";

async function editableFiles(outDir: string): Promise<string[]> {
  // The AUTHORED sources: the reviser edits these, and the pipeline reassembles
  // paper.tex from them (P2 reassemble mode) so revisions persist in the sources
  // and survive later re-entries/redrafts instead of living only in paper.tex.
  return [join(outDir, "front_matter.tex"), ...(await texFilesUnder(outDir, ["sections", "proofs"]))];
}

function protectedFiles(outDir: string): string[] {
  return [
    join(outDir, "formal_layer.json"),
    join(outDir, "formal_layer.tex"),
    join(outDir, "formal_layer_web.json"),
    join(outDir, "verification_contract.json"),
    join(outDir, "presentation_crosswalk.json"),
    join(outDir, "lean_snippets.json"),
    join(outDir, "paper_graph.json"),
  ];
}

function protectedAuthoredCaches(outDir: string): string[] {
  // outline.md is protected: the section set/order is P1's job — a structural
  // finding routes to a P1 re-plan, never to this reviser. paper.tex and
  // appendix_proofs.tex are DERIVED (P2 reassembles them from the edited sources).
  return [
    join(outDir, "outline.md"),
    join(outDir, "references.bib"),
    join(outDir, "paper.tex"),
    join(outDir, "appendix_proofs.tex"),
  ];
}

/** Same-process before/after comparison only — absolute-path labels, missing files tolerated. */
const contentDigest = (paths: string[]): Promise<string> => digestPaths(paths, { missingAsEmpty: true });

// P4 owns these purely derived publishable views of the authored manuscript. If
// P5 changes an editable source, retaining any one of them would make a directory
// look publishable while mixing revisions. Do not re-emit here: P3 must first
// gate the revision, and a full P4 re-emit is expensive (LaTeX plus citation
// verification). `paper_library_index.json` is deliberately retained: it is a
// decl-level Lean index whose contents do not depend on prose, and P4 writes it
// best-effort while the site requires a non-empty index for Lean-backed entries.
// `meta.json` is also deliberately retained: it carries sticky TL;DR and scoring
// state, and its presence keeps an interrupted revision visible to site integrity
// checks rather than silently dropping the bundle. The pipeline immediately runs
// P3 -> P4 after a changed P5 pass; until then, the remaining absent derived
// inputs make the mixed-revision bundle fail those checks loudly.
const P4_DERIVED_ARTIFACTS = [
  "paper.pdf",
  "paper_body.html",
  "lean_snippets.json",
  "presentation_crosswalk.json",
  "paper_graph.json",
  "formal_layer_web.json",
  "assumption_table.md",
];

async function invalidateP4DerivedArtifacts(outDir: string): Promise<void> {
  await Promise.all(P4_DERIVED_ARTIFACTS.map((name) => rm(join(outDir, name), { force: true })));
}

export async function stageP5HolisticRevision(
  io: StageIO,
  review: PriorReview,
  repairable: PriorReview["findings"],
): Promise<{ changed: boolean; fingerprints: string[] }> {
  if (io.ctx.deps.dryRun) {
    await writeFile(join(io.outDir, "p5_holistic_revision.stub"), "dry-run\n");
    return { changed: true, fingerprints: repairable.map(findingFingerprint).sort() };
  }
  const files = await editableFiles(io.outDir);
  const sourceBefore = new Map<string, string>();
  for (const path of files) sourceBefore.set(path, await readFile(path, "utf8").catch(() => ""));
  const before = await contentDigest(files);
  const protectedPaths = [...protectedFiles(io.outDir), ...protectedAuthoredCaches(io.outDir)];
  const protectedBefore = await contentDigest(protectedPaths);
  const formalLayer = FormalLayerSource.safeParse(
    JSON.parse(await readFile(join(io.outDir, "formal_layer.json"), "utf8").catch(() => "{}")),
  );
  const verificationContract = await readFile(join(io.outDir, "verification_contract.json"), "utf8");
  const relatedWork = await readFile(join(io.outDir, "related_work_brief.md"), "utf8").catch(() => "");
  const pass = io.state.p5_revision_passes + 1;
  const mode = revisionMode(repairable);
  // Context parity with an orchestrator revision: the reviser sees the FULL review
  // (blocked findings marked context-only) and the research-stage narrative/charter,
  // not just the routed rewrite subset.
  const repairableSet = new Set(repairable);
  const blocked = review.findings.filter((f) => !repairableSet.has(f));
  const narrative = await loadBankNarrative(io.ctx.repoRoot, io.ctx.qid, io.ctx.spec).catch(() => null);
  const narrativeText = narrative
    ? [
        narrative.interpretation && `Interpretation:\n${narrative.interpretation}`,
        narrative.honestScope && `Honest scope (the entry's own do-not-claim charter — never contradict it):\n${narrative.honestScope}`,
      ].filter(Boolean).join("\n\n")
    : "";
  const prompt = await presentationPrompt("p5_holistic_revision", {
    out_dir: io.outDir,
    revision_pass: String(pass),
    revision_mode: mode,
    p5_review: JSON.stringify({ ...review, findings: repairable }, null, 2),
    blocked_findings: blocked.length > 0 ? JSON.stringify(blocked, null, 2) : "(none)",
    contribution_narrative: narrativeText || "(none recorded)",
    verification_contract: verificationContract,
    related_work_brief: relatedWork,
    editable_files: files.map((path) => `- ${path}`).join("\n"),
  });
  const { stdout } = await io.ctx.deps.runCodex({
    prompt,
    cwd: io.outDir,
    reasoningEffort: "high",
    leanLsp: false,
    model: MODELS.codexPresentation,
    multiAgent: false,
  });
  const protectedAfter = await contentDigest(protectedPaths);
  if (protectedAfter !== protectedBefore) {
    throw new Error("P5 holistic reviser modified a protected formal or derived artifact (outline.md, references.bib, paper.tex, appendix_proofs.tex and the formal layer are not editable — edit the authored sources); restore it before continuing.");
  }
  if (formalLayer.success) {
    const restoredByPath = new Map<string, string>();
    for (const path of files.filter((p) => p.endsWith(".tex"))) {
      const revised = await readFile(path, "utf8").catch(() => "");
      const restored = applyProseRevision({
        before: sourceBefore.get(path) ?? "",
        revised,
        blocks: formalLayer.data.blocks,
        who: "P5 holistic reviser",
      });
      if (restored !== revised) restoredByPath.set(path, restored);
    }
    // Validate every authored file before writing any repair. A cross-file move
    // discovered late in the scan must not leave earlier files half-restored.
    for (const [path, restored] of restoredByPath) await writeFile(path, restored, "utf8");
  }
  const after = await contentDigest(files);
  if (after !== before) await invalidateP4DerivedArtifacts(io.outDir);
  await writeFile(
    join(io.outDir, `p5_revision_pass_${pass}.md`),
    `# Holistic revision pass ${pass}\n\n- mode: ${mode}\n- source digest before: \`${before}\`\n- source digest after: \`${after}\`\n\n## Reviser report\n\n${stdout.trim()}\n`,
    "utf8",
  );
  return { changed: before !== after, fingerprints: repairable.map(findingFingerprint).sort() };
}
