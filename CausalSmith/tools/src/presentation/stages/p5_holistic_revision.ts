import { createHash } from "node:crypto";
import { readdir, readFile, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { presentationPrompt } from "../prompt_io.js";
import type { StageIO } from "../pipeline.js";
import type { PriorReview } from "../revision_brief.js";
import { findingFingerprint, revisionMode } from "../revision_routing.js";
import { MODELS } from "../../models.js";
import { FormalLayerSource, normalizeCitedScopeFootnotes, texEnvFor, type FormalBlock } from "../formal_layer.js";
import { normalizeFrozenEnvs, parseAnchoredEnvs } from "../tex_anchors.js";

async function editableFiles(outDir: string): Promise<string[]> {
  const paths = [
    join(outDir, "outline.md"),
    join(outDir, "front_matter.tex"),
    join(outDir, "appendix_proofs.tex"),
    join(outDir, "references.bib"),
    join(outDir, "paper.tex"),
  ];
  for (const dir of ["sections", "proofs"]) {
    const names = await readdir(join(outDir, dir)).catch(() => []);
    paths.push(...names.filter((name) => name.endsWith(".tex")).sort().map((name) => join(outDir, dir, name)));
  }
  return paths;
}

function protectedFiles(outDir: string): string[] {
  return [
    join(outDir, "formal_layer.json"),
    join(outDir, "formal_layer.tex"),
    join(outDir, "formal_layer_web.json"),
    join(outDir, "verification_contract.json"),
    join(outDir, "presentation_crosswalk.json"),
    join(outDir, "lean_snippets.json"),
  ];
}

async function contentDigest(paths: string[]): Promise<string> {
  const hash = createHash("sha256");
  for (const path of paths) {
    hash.update(path);
    hash.update("\0");
    hash.update(await readFile(path).catch(() => Buffer.from("")));
    hash.update("\0");
  }
  return hash.digest("hex");
}

/**
 * Reinsert any frozen environments that a holistic prose revision deleted.
 * Existing bodies are first reset to their canonical text. Missing blocks are
 * placed relative to their nearest surviving neighbour in the pre-revision
 * source, so the reviser's surrounding prose is preserved. Adding or moving an
 * anchored environment across authored files is rejected: P5 is a manuscript
 * revision stage, not a formal-layer editor.
 */
export function restoreFrozenEnvsAfterRevision(
  before: string,
  revised: string,
  canonical: Map<string, string>,
): string {
  const beforeIds = parseAnchoredEnvs(before).map((e) => e.obj_id).filter((id) => canonical.has(id));
  const beforeSet = new Set(beforeIds);
  const revisedIds = parseAnchoredEnvs(revised).map((e) => e.obj_id).filter((id) => canonical.has(id));
  const added = revisedIds.filter((id) => !beforeSet.has(id));
  if (added.length > 0) {
    throw new Error(`P5 holistic reviser moved/added frozen environment(s): ${[...new Set(added)].join(", ")}`);
  }
  const duplicate = revisedIds.find((id, i) => revisedIds.indexOf(id) !== i);
  if (duplicate) throw new Error(`P5 holistic reviser duplicated frozen environment: ${duplicate}`);
  const survivingOrder = beforeIds.filter((id) => revisedIds.includes(id));
  if (revisedIds.some((id, i) => id !== survivingOrder[i])) {
    throw new Error("P5 holistic reviser reordered frozen environments");
  }
  if (beforeIds.length === 0) return revised;

  let out = normalizeFrozenEnvs(revised, canonical);
  for (let i = 0; i < beforeIds.length; i++) {
    const id = beforeIds[i];
    if (parseAnchoredEnvs(out).some((e) => e.obj_id === id)) continue;
    const env = canonical.get(id)!;
    const present = new Set(parseAnchoredEnvs(out).map((e) => e.obj_id));
    const next = beforeIds.slice(i + 1).find((candidate) => present.has(candidate));
    const prev = [...beforeIds.slice(0, i)].reverse().find((candidate) => present.has(candidate));
    if (next) {
      const marker = canonical.get(next)!;
      const at = out.indexOf(marker);
      if (at >= 0) {
        out = `${out.slice(0, at)}${env}\n\n${out.slice(at)}`;
        continue;
      }
    }
    if (prev) {
      const marker = canonical.get(prev)!;
      const at = out.indexOf(marker);
      if (at >= 0) {
        const end = at + marker.length;
        out = `${out.slice(0, end)}\n\n${env}${out.slice(end)}`;
        continue;
      }
    }
    out = `${out.replace(/\s*$/, "")}\n\n${env}\n`;
  }
  return normalizeFrozenEnvs(out, canonical);
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
  const protectedBefore = await contentDigest(protectedFiles(io.outDir));
  const formalLayer = FormalLayerSource.safeParse(
    JSON.parse(await readFile(join(io.outDir, "formal_layer.json"), "utf8").catch(() => "{}")),
  );
  const verificationContract = await readFile(join(io.outDir, "verification_contract.json"), "utf8");
  const relatedWork = await readFile(join(io.outDir, "related_work_brief.md"), "utf8").catch(() => "");
  const pass = io.state.p5_revision_passes + 1;
  const mode = revisionMode(repairable);
  const prompt = await presentationPrompt("p5_holistic_revision", {
    out_dir: io.outDir,
    revision_pass: String(pass),
    revision_mode: mode,
    p5_review: JSON.stringify({ ...review, findings: repairable }, null, 2),
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
  const protectedAfter = await contentDigest(protectedFiles(io.outDir));
  if (protectedAfter !== protectedBefore) {
    throw new Error("P5 holistic reviser modified a protected formal/crosswalk artifact; restore it before continuing.");
  }
  if (formalLayer.success) {
    const envBlocks = formalLayer.data.blocks.filter((b): b is FormalBlock & { env: NonNullable<FormalBlock["env"]> } => b.env != null);
    const canonical = new Map(envBlocks.map((b) => [b.obj_id, texEnvFor(b)]));
    const restoredByPath = new Map<string, string>();
    for (const path of files.filter((p) => p.endsWith(".tex"))) {
      const revised = await readFile(path, "utf8").catch(() => "");
      let restored = restoreFrozenEnvsAfterRevision(sourceBefore.get(path) ?? "", revised, canonical);
      restored = normalizeCitedScopeFootnotes(restored, envBlocks);
      if (restored !== revised) restoredByPath.set(path, restored);
    }
    // Validate every authored file before writing any repair. A cross-file move
    // discovered late in the scan must not leave earlier files half-restored.
    for (const [path, restored] of restoredByPath) await writeFile(path, restored, "utf8");
  }
  const after = await contentDigest(files);
  await writeFile(
    join(io.outDir, `p5_revision_pass_${pass}.md`),
    `# Holistic revision pass ${pass}\n\n- mode: ${mode}\n- source digest before: \`${before}\`\n- source digest after: \`${after}\`\n\n## Reviser report\n\n${stdout.trim()}\n`,
    "utf8",
  );
  return { changed: before !== after, fingerprints: repairable.map(findingFingerprint).sort() };
}
