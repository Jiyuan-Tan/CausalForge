import { mkdir, readdir, readFile, rename, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { join } from "node:path";
import type { StageIO } from "../pipeline.js";
import { presentationPrompt, promptFingerprint } from "../prompt_io.js";
import { hashEnvBody } from "../tex_anchors.js";
import { lintSlides, parseSlidesMd, type FormalBlockRef } from "../slides.js";
import { parseFigureDsl, renderFigureSvg } from "../figure_layout.js";

/**
 * P6 — seminar slides. Terminal, optional, and strictly post-P5: a derived,
 * compressed pitch-talk view of the FINISHED paper (see
 * internal/plans/2026-08-27-p6-slides-proposal.md). One codex call emits
 * `slides.md`; formal statements are injected from the frozen layer at render
 * time, so no equivalence/proof re-audit runs here. `slides.md` is an AUTHORED
 * SOURCE: hand edits survive regeneration (refused without ctx.refreshSlides),
 * and the quality gate is the orchestrator reading it — clarity is the measure.
 */
export async function stageP6(io: StageIO): Promise<void> {
  if (io.ctx.deps.dryRun) {
    await writeFile(join(io.outDir, "p6.stub"), "dry-run\n");
    return;
  }
  const meta = JSON.parse(await readFile(join(io.outDir, "meta.json"), "utf8")) as {
    title: string;
    tldr?: string;
    abstract: string;
  };
  const layer = JSON.parse(await readFile(join(io.outDir, "formal_layer.json"), "utf8")) as {
    blocks: { obj_id: string; alias?: string | null; kind: string; title: string; body: string }[];
  };
  const outline = await readFile(join(io.outDir, "outline.md"), "utf8");
  const brief = await readFile(join(io.outDir, "related_work_brief.md"), "utf8").catch(() => "");
  // Appendix sections are proof detail the deck must not show anyway; dropping
  // them first keeps the budget for main-text prose. A flat tail-truncation
  // would deterministically cut the RESULTS sections (numbered last), so over
  // budget every section is clipped proportionally instead.
  const sectionNames = (await readdir(join(io.outDir, "sections")).catch(() => []))
    .filter((n) => n.endsWith(".tex") && !/appendix/i.test(n))
    .sort();
  const rawSections = await Promise.all(
    sectionNames.map((n) => readFile(join(io.outDir, "sections", n), "utf8")),
  );
  const SECTIONS_BUDGET = 60_000;
  const sectionsTotal = rawSections.reduce((s, t) => s + t.length, 0);
  let sections: string;
  if (sectionsTotal <= SECTIONS_BUDGET) {
    sections = rawSections.join("\n\n");
  } else {
    sections = rawSections
      .map((t) => t.slice(0, Math.floor((t.length / sectionsTotal) * SECTIONS_BUDGET)))
      .join("\n\n");
    io.state.notes.push(
      `P6: paper sections exceed the prompt budget (${sectionsTotal} > ${SECTIONS_BUDGET} chars) — each section clipped proportionally.`,
    );
  }

  const key = hashEnvBody(
    [
      await promptFingerprint("p6_slides"),
      meta.title,
      meta.tldr ?? "",
      meta.abstract,
      outline,
      brief,
      sections,
      ...layer.blocks.map((b) => `${b.obj_id}§${b.body}`),
    ].join("§§"),
  );
  const cachePath = join(io.outDir, "slides_cache.json");
  const slidesPath = join(io.outDir, "slides.md");
  const cache = await readFile(cachePath, "utf8")
    .then((raw) => JSON.parse(raw) as { key: string; generated_hash: string })
    .catch(() => null);
  const existing = await readFile(slidesPath, "utf8").catch(() => null);
  // No cache sidecar next to an existing slides.md (deleted, corrupt, or a crash
  // between the two writes): provenance is unknown, so FAIL CLOSED — treat the
  // deck as hand-edited rather than silently regenerating over possible edits.
  if (existing !== null) {
    const handEdited = cache === null || hashEnvBody(existing) !== cache.generated_hash;
    // Both kept-deck paths still author any figure whose asset is missing (a hand
    // edit may ADD an @figure; a prior run may have died mid-figure-authoring).
    if (handEdited && io.ctx.refreshSlides !== true) {
      const authored = await authorMissingFigures(io, parseSlidesMd(existing), meta.abstract, layer.blocks);
      io.state.notes.push(
        `P6: slides.md has hand edits — kept as-is (regenerate with --refresh-slides to discard them)${authored > 0 ? `; ${authored} figure(s) authored` : ""}.`,
      );
      return;
    }
    if (!handEdited && cache !== null && cache.key === key) {
      const authored = await authorMissingFigures(io, parseSlidesMd(existing), meta.abstract, layer.blocks);
      io.state.notes.push(`P6: slides.md up to date (cache hit)${authored > 0 ? `; ${authored} figure(s) authored` : ""}.`);
      return;
    }
  }

  // Paper-labeled blocks first (stable order); a null alias marks an internal
  // helper — flag it explicitly so the "never reference helpers" rule is followable.
  const formalCatalog = [...layer.blocks]
    .sort((a, b) => Number(b.alias != null) - Number(a.alias != null))
    .map(
      (b) =>
        `- ${b.obj_id} | ${b.kind} | ${b.alias ?? "(internal helper — never reference on a slide)"} | ${b.title}\n${b.body}`,
    )
    .join("\n\n");
  const formalRefs: FormalBlockRef[] = layer.blocks.map((b) => ({ obj_id: b.obj_id, kind: b.kind }));
  const vars = {
    title: meta.title,
    tldr: meta.tldr ?? "",
    abstract: meta.abstract,
    outline,
    related_work_brief: brief,
    formal_catalog: formalCatalog,
    sections,
    lint_findings: "",
  };

  // One call; one lint-informed retry; then halt for the orchestrator. There is no
  // model review loop — the deck's judge is the orchestrator at the checkpoint.
  let md = await generate(io, vars);
  let problems = lintDeck(md, formalRefs);
  if (problems.length > 0) {
    // Minimal-repair retry: a fresh re-roll can regress on dimensions the lint
    // does not check (drop a figure, rename a coined term, break a cross-slide
    // reference) — so the retry patches the previous deck instead.
    md = await generate(io, {
      ...vars,
      lint_findings:
        "\nA previous attempt failed these mechanical checks — fix ALL of them:\n" +
        problems.map((p) => `- [${p.gate}] ${p.detail}`).join("\n") +
        "\nRepair MINIMALLY: reproduce the previous deck below unchanged except where a listed defect requires an edit — do not drop, rename, or rewrite slides, figures, or terms that are not implicated.\n\nPrevious deck:\n" +
        md + "\n",
    });
    problems = lintDeck(md, formalRefs);
    if (problems.length > 0) {
      throw new Error(
        `P6: slides failed the mechanical lint after one retry:\n- ${problems
          .map((p) => `[${p.gate}] ${p.detail}`)
          .join("\n- ")}`,
      );
    }
  }
  // Atomic (tmp+rename) writes, cache FIRST: a crash between the writes can
  // only leave a cache mismatching the (old or absent) deck — the next run then
  // fails CLOSED, keeping the old deck as "hand-edited" until --refresh-slides.
  // Never a fresh deck without provenance, and NFS readers never see torn files.
  const finalMd = md.endsWith("\n") ? md : md + "\n";
  await writeAtomic(
    cachePath,
    JSON.stringify({ key, generated_hash: hashEnvBody(finalMd) }, null, 2) + "\n",
  );
  await writeAtomic(slidesPath, finalMd);
  const deck = parseSlidesMd(md);
  const authored = await authorMissingFigures(io, deck, meta.abstract, layer.blocks);
  io.state.notes.push(
    `P6: wrote slides.md (${deck.slides.length} slides${authored > 0 ? `, ${authored} figure(s) authored` : ""}) — review for clarity at the checkpoint; hand edits are the fix path.`,
  );
}

/** One codex call per @figure whose `slides_assets/<name>.svg` does not exist yet.
 *  Existing assets (including hand-drawn replacements) are never overwritten —
 *  delete a file to re-author it. Figures are schematics labeled "illustrative";
 *  the orchestrator judges them at the clarity checkpoint like everything else. */
async function authorMissingFigures(
  io: StageIO,
  deck: ReturnType<typeof parseSlidesMd>,
  abstract: string,
  blocks: { obj_id: string; kind: string; body: string }[],
): Promise<number> {
  const bodyOf = new Map(blocks.map((b) => [b.obj_id, b]));
  const wanted: {
    name: string;
    caption: string;
    slideTitle: string;
    slideContent: string;
    formalContext: string;
  }[] = [];
  for (const slide of deck.slides) {
    for (const block of slide.blocks) {
      if (block.kind !== "figure") continue;
      const slideContent = slide.blocks
        .map((b) => (b.kind === "prose" ? b.md : b.kind === "informal" ? b.text : ""))
        .filter(Boolean)
        .join("\n");
      // The figure model must see the audited definitions its arrows depict —
      // caption + prose alone produced dependency-wrong diagrams (audit 2026-08-27).
      const formalContext = slide.blocks
        .flatMap((b) => (b.kind === "formal" || b.kind === "informal" ? [b.objId] : []))
        .flatMap((id) => {
          const fb = bodyOf.get(id);
          return fb ? [`${fb.obj_id} (${fb.kind}):\n${fb.body}`] : [];
        })
        .join("\n\n");
      wanted.push({ name: block.name, caption: block.caption, slideTitle: slide.title, slideContent, formalContext });
    }
  }
  if (wanted.length === 0) return 0;
  const assetsDir = join(io.outDir, "slides_assets");
  await mkdir(assetsDir, { recursive: true });
  let authored = 0;
  for (const fig of wanted) {
    const path = join(assetsDir, `${fig.name}.svg`);
    if (existsSync(path)) continue;
    const vars = {
      name: fig.name,
      caption: fig.caption,
      slide_title: fig.slideTitle,
      slide_content: fig.slideContent,
      formal_context: fig.formalContext || "(none referenced on this slide)",
      abstract,
      dsl_findings: "",
    };
    // Content from the model, geometry from figure_layout — one DSL-informed retry.
    let dsl = "";
    let svg: string;
    try {
      dsl = extractDsl(await runFigureCall(io, vars));
      svg = renderFigureSvg(parseFigureDsl(dsl));
    } catch (err) {
      const detail = err instanceof Error ? err.message : String(err);
      dsl = extractDsl(
        await runFigureCall(io, {
          ...vars,
          dsl_findings: `\nA previous attempt failed: ${detail}\n${dsl ? `Its DSL was:\n${dsl}\n` : ""}Emit ONLY valid DSL lines this time.\n`,
        }),
      );
      svg = renderFigureSvg(parseFigureDsl(dsl));
    }
    await writeAtomic(path, svg);
    // The DSL is the figure's SOURCE: kept beside the SVG so a layouter improvement
    // (or a content hand-fix) can re-render without a model call.
    await writeAtomic(join(assetsDir, `${fig.name}.dsl`), dsl + "\n");
    authored += 1;
  }
  return authored;
}

async function runFigureCall(io: StageIO, vars: Record<string, string>): Promise<string> {
  const prompt = await presentationPrompt("p6_figure", vars);
  const { stdout } = await io.ctx.deps.runCodex({
    prompt,
    cwd: io.ctx.repoRoot,
    reasoningEffort: "medium",
    leanLsp: false,
  });
  return stdout;
}

/** tmp+rename so concurrent readers (and a crash mid-write) never see a torn file. */
async function writeAtomic(path: string, content: string): Promise<void> {
  const tmp = `${path}.tmp-${process.pid}`;
  await writeFile(tmp, content, "utf8");
  await rename(tmp, path);
}

/** Keep only DSL statements — models sometimes wrap output in fences or preamble. */
export function extractDsl(stdout: string): string {
  const lines = stdout
    .replace(/```[a-z]*\n?/g, "")
    .split("\n")
    .map((l) => l.trim())
    .filter((l) => /^(node|edge)\s/.test(l));
  if (lines.length === 0) throw new Error("model output contains no `node`/`edge` DSL lines");
  return lines.join("\n");
}

async function generate(io: StageIO, vars: Record<string, string>): Promise<string> {
  const prompt = await presentationPrompt("p6_slides", vars);
  const { stdout } = await io.ctx.deps.runCodex({
    prompt,
    cwd: io.ctx.repoRoot,
    reasoningEffort: "high",
    leanLsp: false,
  });
  return extractDeckMarkdown(stdout);
}

/** Strip codex chatter/fences: the deck starts at the first `# ` heading line. */
export function extractDeckMarkdown(stdout: string): string {
  let text = stdout.trim();
  // Strip a fence only when it CLOSES AT THE END of the output (leading chatter
  // before the opener is fine). A fully line-anchored (/m) match would pair an
  // internal fence mid-deck and truncate the deck to that block's interior.
  const fence = /(?:^|\n)```(?:markdown|md)?\n([\s\S]*?)\n```\s*$/.exec(text);
  if (fence) text = fence[1].trim();
  const start = text.search(/^# /m);
  if (start < 0) throw new Error("P6: model output contains no `# <talk title>` heading");
  return text.slice(start).trim() + "\n";
}

function lintDeck(md: string, formalRefs: FormalBlockRef[]) {
  try {
    return lintSlides(parseSlidesMd(md), formalRefs);
  } catch (err) {
    return [{ gate: "slides-structure", detail: err instanceof Error ? err.message : String(err) }];
  }
}
