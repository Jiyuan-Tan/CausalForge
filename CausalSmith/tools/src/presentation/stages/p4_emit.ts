import { readFile, writeFile, mkdir, rename, rm } from "node:fs/promises";
import { basename, join } from "node:path";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import type { StageIO } from "../pipeline.js";
import { presentationPrompt } from "../prompt_io.js";
import { parseOutline, reconcileXrefAdvisories } from "../stage_util.js";
import { parseAnchoredEnvs, lintAnchors, lintClarity, lintDefinitionOrder, lintNegativeContributionFraming, lintNestedMathDelimiters, lintReferences, repairObjRefs } from "../tex_anchors.js";
import { FormalLayerSource, normalizeCitedScopeFootnotes, paperEnvMismatches } from "../formal_layer.js";
import { parseNoteBlocks } from "../note_parser.js";
import { SYNTHETIC_COMPANION_RE, externallyConsumedModules, findOrphanPaperModules } from "../paper_index_orphans.js";
import { parseBib, verifyEntry, defaultLookup, citedKeys, canonicalizeBibEntry, UNREACHABLE } from "../citations.js";
import { buildBundle, buildProseEntries, buildFormalLayer, buildSymbolRealizations, assumptionTable } from "../emit.js";
import { discoverRealizedSymbols, buildSymbolClusters } from "../../formalization/crosswalk.js";
import { auxiliaryNodes, isCitedNode } from "../graph_view.js";
import { ensureComponentsForEnvs } from "../components.js";
import { extractLeanrefIds } from "../tex2html.js";
import { paperReferenceLabels, resolveObjCrefsPlain, tex2html } from "../tex2html.js";
import { PresentationCrosswalk, LeanSnippets, FormalLayer, PaperMeta } from "../types.js";
import { MODELS } from "../../models.js";
import { assertP2AssemblyFresh, recordP2Assembly, texFilesUnder } from "../assembly_freshness.js";
import { loadJsonCache } from "../cache.js";
import { buildPaperGraph, lintIsolatedLemmas, type PaperGraphNode } from "../paper_graph.js";

const execFileP = promisify(execFile);
const COMPILE_ATTEMPTS = 3;

type IndexedDecl = {
  name?: unknown;
  source?: unknown;
  doc?: unknown;
  module?: unknown;
  file?: unknown;
  statement?: unknown;
  kind?: unknown;
  line?: unknown;
};

type PaperLibraryIndex = {
  modules?: Record<string, unknown>;
  entries?: IndexedDecl[];
};

const INDEXED_FIELDS = ["source", "doc", "module", "file", "statement", "kind", "line"] as const;

function parsePaperLibraryIndex(raw: string, path: string): PaperLibraryIndex {
  const index = JSON.parse(raw) as PaperLibraryIndex;
  if (!Array.isArray(index.entries)) throw new Error(`P4: ${path} has no entries array`);
  return index;
}

async function readPaperLibraryIndex(path: string): Promise<PaperLibraryIndex | null> {
  try {
    return parsePaperLibraryIndex(await readFile(path, "utf8"), path);
  } catch (err: unknown) {
    if ((err as NodeJS.ErrnoException).code === "ENOENT") return null;
    throw err;
  }
}

function hasSourceLocation(entry: IndexedDecl): entry is IndexedDecl & { name: string; source: string; line: number } {
  return typeof entry.name === "string" && typeof entry.source === "string" && entry.source.length > 0 &&
    typeof entry.line === "number" && entry.line > 0;
}

/** Reject a candidate cache that would silently erase an existing published declaration or field.
`congr_simp`-style synthetic constants have no authored source/range and are intentionally excluded
from this comparison: the extractor omits them rather than publishing an unusable drawer entry. */
function validatePaperIndexReplacement(
  previous: PaperLibraryIndex | null,
  next: PaperLibraryIndex,
  moduleTargets: string[],
): void {
  const nextEntries = next.entries!;
  if (moduleTargets.length > 0 && nextEntries.length === 0)
    throw new Error("P4: paper_index emitted an empty index for non-empty module targets");
  if (!previous) return;
  const byName = new Map(nextEntries.flatMap((entry) =>
    typeof entry.name === "string" ? [[entry.name, entry] as const] : [],
  ));
  const lost = previous.entries!.filter(hasSourceLocation).flatMap((entry) =>
    // Synthetic companions in an older cache may carry a borrowed source slice
    // or an `add_decl_doc` range; the extractor now omits them by design.
    byName.has(entry.name) || SYNTHETIC_COMPANION_RE.test(entry.name) ? [] : [entry.name],
  );
  if (lost.length > 0)
    throw new Error(`P4: paper_index would drop ${lost.length} published declaration(s): ${lost.slice(0, 12).join(", ")}`);
  const nulled: string[] = [];
  for (const oldEntry of previous.entries!.filter(hasSourceLocation)) {
    const current = byName.get(oldEntry.name);
    if (!current) continue;
    for (const field of INDEXED_FIELDS) {
      const before = oldEntry[field];
      const after = current[field];
      if (before !== null && before !== undefined && (after === null || after === undefined))
        nulled.push(`${oldEntry.name}.${field}`);
      if (field === "line" && before !== 0 && after === 0) nulled.push(`${oldEntry.name}.line`);
    }
  }
  if (nulled.length > 0)
    throw new Error(`P4: paper_index would null ${nulled.length} published field(s): ${nulled.slice(0, 12).join(", ")}`);
}

/** Only Lean-backed blocks have a Lean equivalence claim to audit. Presentation-
 * synthesized definitions are frozen and linted, but intentionally have no Lean
 * declaration and therefore no P1 equivalence verdict. EXCEPTION: a lean-null
 * block whose cache entry still records `drift` blocks anyway — otherwise
 * removing a block's Lean mapping would launder a recorded frozen-layer↔Lean
 * disagreement past emission. */
export function blocksMissingEquivalence(
  blocks: Array<{ obj_id: string; lean: unknown | null }>,
  cache: Record<string, { verdict?: string }>,
): Array<{ obj_id: string; lean: unknown | null }> {
  return blocks.filter((b) =>
    b.lean !== null
      ? cache[b.obj_id]?.verdict !== "faithful"
      : cache[b.obj_id]?.verdict === "drift",
  );
}

/**
 * P4 — emit the bundle: final lint, citation re-verification, PDF compile
 * loop (Terra fixes LaTeX errors, never frozen bodies), mechanical crosswalk
 * join + Lean snippet extraction, assumption-faithfulness table with totality
 * check, tex→HTML fragment, meta.json. Site consumes only these artifacts.
 */
export async function stageP4(io: StageIO): Promise<void> {
  await mkdir(io.outDir, { recursive: true });
  if (io.ctx.deps.dryRun) {
    await writeFile(join(io.outDir, "p4.stub"), "dry-run\n");
    return;
  }
  // P4 is the supported deterministic re-emit entrypoint, so it must refresh template-owned
  // macros instead of inheriting the copy last written by P2. Otherwise a template change can
  // spuriously enter the model-driven LaTeX repair loop and get patched into paper.tex itself.
  const macros = await readFile(join(import.meta.dirname, "..", "templates", "paper_macros.tex"), "utf8");
  await writeFile(join(io.outDir, "paper_macros.tex"), macros, "utf8");
  // Equivalence is the trust anchor, and the standard re-emit path `--from P4`
  // skips the earlier stages — so emission must re-consult the persistent cache
  // (live incident: P-8 shipped with verdict="drift" while hard_gate_failures
  // was 0). `blocksMissingEquivalence` below blocks every Lean-backed block
  // whose current verdict is not `faithful` (drift, missing, or unparseable),
  // plus any retained lean-null block still carrying a `drift` verdict.
  const equivalenceCache = await loadJsonCache<Record<string, { verdict?: string; detail?: string }>>(
    join(io.outDir, "equivalence_cache.json"),
  );
  const paperPath = join(io.outDir, "paper.tex");
  let paperTex = await readFile(paperPath, "utf8");
  await assertP2AssemblyFresh(io.outDir);
  // Formal layer (source of truth); the freeze IS each block's `body` — env bodies are compared against it.
  const formalLayer = FormalLayerSource.parse(
    JSON.parse(await readFile(join(io.outDir, "formal_layer.json"), "utf8")),
  );
  // The disclosure is generated from the formal graph, so repair it deterministically at the
  // final emission boundary as well. This makes `--from P4` sufficient after a template change and
  // prevents a prose revision from dropping either the heading marker or the exact scope text.
  const normalizedScopeTex = normalizeCitedScopeFootnotes(paperTex, formalLayer.blocks);
  if (normalizedScopeTex !== paperTex) {
    paperTex = normalizedScopeTex;
    await writeFile(paperPath, paperTex, "utf8");
  }
  const unaudited = blocksMissingEquivalence(formalLayer.blocks, equivalenceCache);
  if (unaudited.length > 0) {
    const details = unaudited
      .map((b) => `[${b.obj_id}] ${equivalenceCache[b.obj_id]?.verdict ?? "missing"}: ${equivalenceCache[b.obj_id]?.detail ?? ""}`)
      .join("; ");
    throw new Error(
      `P4 blocked: ${unaudited.length} formal-layer object(s) lack a current faithful P1 equivalence verdict ` +
        `(${unaudited.map((b) => b.obj_id).join(", ")}). Amend the frozen body so a fresh P1 audit passes ` +
        `(the content-keyed cache invalidates on the body change), or — for an auditor false positive, or a ` +
        `lean-null block with a lingering drift verdict — reseed that entry to faithful; P4 will not emit an ` +
        `unaudited correspondence panel. ${details}`,
    );
  }
  const frozen = new Map<string, string>(formalLayer.blocks.map((b) => [b.obj_id, b.body]));
  // The emitted namespace is the frozen formal layer, which also contains
  // presentation-synthesized definitions absent from the accepted-bank graph.
  const known = new Set(formalLayer.blocks.map((b) => b.obj_id));
  // Guard cleveref object ids: an orchestrator hand-edit of paper.tex in a revision pass can
  // reintroduce a prefix-dropped or dangling ref (silent "??"). Repair the unique-prefix case and
  // persist; a residual dangling ref fails the stage.
  const definedIds = new Set(parseAnchoredEnvs(paperTex).map((e) => e.obj_id));
  const notation = parseOutline(await readFile(join(io.outDir, "outline.md"), "utf8")).notation;
  const refRepair = repairObjRefs(paperTex, definedIds);
  if (refRepair.tex !== paperTex) {
    paperTex = refRepair.tex;
    await writeFile(paperPath, paperTex, "utf8");
  }
  const finalLint = [
    ...lintAnchors(paperTex, known, frozen),
    ...lintDefinitionOrder(paperTex, notation),
    ...lintClarity(paperTex),
    ...lintNestedMathDelimiters(paperTex),
    ...lintReferences(paperTex),
    ...lintNegativeContributionFraming(paperTex),
    ...lintIsolatedLemmas(paperTex),
    ...refRepair.problems,
  ];
  if (finalLint.length > 0) {
    throw new Error(`P4 entry lint failed: ${finalLint.map((p) => p.detail).join("; ")}`);
  }
  // citation re-verification on the final pool — only entries ACTUALLY cited in
  // the paper. Uncited bib entries never reach the compiled bibliography, so a
  // dead entry (e.g. a pre-DOI classic that an external registry cannot match on
  // title) must not block the emit.
  const bibPath = join(io.outDir, "references.bib");
  let bibText = await readFile(bibPath, "utf8");
  let bib = parseBib(bibText);
  const cited = citedKeys(paperTex);
  const lookup = io.ctx.deps.lookup ?? defaultLookup;
  for (const entry of bib) {
    if (!cited.has(entry.key)) continue;
    const rec = await lookup(entry);
    let v = await verifyEntry(entry, async () => rec);
    // Safe bibliography healing: an entry's own DOI/arXiv id resolved to exactly one
    // authoritative record. Normalize canonical fields, then verify the repaired entry.
    if (v.verdict === "minor" && rec !== null && rec !== UNREACHABLE && rec.authoritative) {
      const fixed = canonicalizeBibEntry(bibText, entry.key, rec);
      if (fixed !== null && fixed !== bibText) {
        bibText = fixed;
        await writeFile(bibPath, bibText, "utf8");
        const repaired = parseBib(bibText).find((e) => e.key === entry.key)!;
        v = await verifyEntry(repaired, async () => rec);
        io.state.notes.push(`P4: normalized bib entry ${entry.key} from its authoritative DOI/arXiv record.`);
      }
    }
    if (v.verdict === "major") {
      throw new Error(`P4: bib entry ${entry.key} failed re-verification: ${v.detail}`);
    }
    if (v.verdict === "minor") {
      // A transient-unreachable or field-caveat entry is kept (not a hard fail), but surfaced so a
      // network blip / registry gap during the emit is visible rather than silently passed.
      io.state.notes.push(`P4: bib entry ${entry.key} kept with caveat: ${v.detail}`);
    }
  }
  bib = parseBib(bibText);

  // compile loop
  let lastLog = "";
  let compiled = false;
  for (let attempt = 1; attempt <= COMPILE_ATTEMPTS && !compiled; attempt++) {
    try {
      await execFileP("latexmk", ["-pdf", "-interaction=nonstopmode", "paper.tex"], {
        cwd: io.outDir,
        maxBuffer: 64 * 1024 * 1024,
      });
      compiled = true;
    } catch (e: unknown) {
      const err = e as { stdout?: string; stderr?: string; message?: string };
      lastLog = [err.stdout, err.stderr, err.message].filter(Boolean).join("\n");
      if (attempt === COMPILE_ATTEMPTS) break;
      // codex edits paper.tex in place (user decision 2026-06-10: prefer codex
      // credit; also avoids emitting the full source on stdout). Lint guards;
      // restore on failure.
      const before = paperTex;
      await io.ctx.deps.runCodex({
        prompt: await presentationPrompt("p4_latex_fix", {
          compile_log: lastLog.slice(-8000),
          paper_path: paperPath,
          source_paths: await authoredTexSources(io.outDir),
        }),
        cwd: io.ctx.repoRoot,
        reasoningEffort: "medium",
        leanLsp: false,
        model: MODELS.codexMechanical,
      });
      const fixed = await readFile(paperPath, "utf8");
      const lint = [...lintAnchors(fixed, known, frozen), ...lintDefinitionOrder(fixed, notation)];
      if (lint.length > 0) {
        // Restore and RETRY rather than aborting the stage: the retry budget exists
        // precisely for this. Feed the lint back so the next attempt knows why the
        // previous edit was rejected instead of re-deriving the same illegal fix.
        const detail = lint.map((p) => p.detail).join("; ");
        await writeFile(paperPath, before, "utf8");
        if (attempt === COMPILE_ATTEMPTS - 1) {
          throw new Error(`P4 LaTeX fix broke the frozen layer on every attempt (restored): ${detail}`);
        }
        lastLog = `${lastLog}\n\nATTEMPT ${attempt} REJECTED AND REVERTED — your edit violated the frozen-layer lint: ${detail}\nDo not repeat that edit; fix the compile error a different way.`;
        continue;
      }
      paperTex = fixed;
    }
  }
  if (!compiled) {
    throw new Error(`P4: paper.tex failed to compile after ${COMPILE_ATTEMPTS} attempts:\n${lastLog.slice(-2000)}`);
  }
  // #5 — surface content that runs off the page. Overfull \hbox warnings are not
  // compile errors (so the fix loop never sees them); read paper.log and report
  // the badly-overfull ones (> 15pt) so the orchestrator can shorten the notation
  // or wrap the wide display/table.
  try {
    const texLog = await readFile(join(io.outDir, "paper.log"), "utf8");
    const bad = [...texLog.matchAll(/Overfull \\hbox \((\d+(?:\.\d+)?)pt too wide\)[^\n]*\n([^\n]*)/g)]
      .map((m) => ({ pt: Number(m[1]), at: m[2].trim().slice(0, 70) }))
      .filter((o) => o.pt > 15)
      .sort((a, b) => b.pt - a.pt);
    if (bad.length > 0) {
      io.state.notes.push(
        `P4 overflow warning (${bad.length} display(s)/line(s) run off the page; shorten the notation or wrap the widest): ${bad
          .slice(0, 5)
          .map((o) => `${o.pt}pt @ "${o.at}"`)
          .join("; ")}`,
      );
    }
  } catch {
    /* no paper.log (dry run) — skip */
  }

  // pin the commit, then index + docstring pass — the extraction below must read the post-docstring tree
  const { stdout: commitRaw } = await execFileP("git", ["rev-parse", "HEAD"], { cwd: io.ctx.repoRoot });
  const commit = commitRaw.trim();
  io.state.pinned_commit = commit;

  // paper-module index: full decl-level view of the run's Lean code for the
  // site's Formalization tab (same extractor core as the Causalean /library
  // explorer). It is a required published artifact: a transient Lake failure
  // must stop P4 rather than leave a stale or blank Formalization tab behind.
  const indexPath = join(io.outDir, "paper_library_index.json");
  // leanSubdir is the module path below the package lib root
  // ("CausalSmith/Stat/X_Research" → module CausalSmith.Stat.X_Research)
  const modPrefix = io.bank.leanSubdir.replace(/\//g, ".");
  const priorIndex = await readPaperLibraryIndex(indexPath);
  // paper_index reads OLEANS, so the paper's modules must be built first or it
  // silently emits an empty index (→ blank Formalization page). Preserve all
  // prior indexed modules as well as crosswalk modules: a useful run helper
  // need not be imported by any crosswalk declaration, while importing every
  // sibling source file changes Lean's source-module ownership.
  const modTargets = [
    ...new Set(
      [
        ...io.bank.crosswalk
          .filter((e) => e.lean)
          .map((e) => `${modPrefix}.${e.lean!.file.replace(/\.lean$/, "").replace(/\//g, ".")}`),
        ...Object.keys(priorIndex?.modules ?? {}).filter((moduleName) =>
          moduleName === modPrefix || moduleName.startsWith(`${modPrefix}.`),
        ),
        ...(priorIndex?.entries ?? []).flatMap((entry) =>
          typeof entry.module === "string" &&
          (entry.module === modPrefix || entry.module.startsWith(`${modPrefix}.`))
            ? [entry.module]
            : [],
        ),
        // Physical-tree modules neither the crosswalk nor a prior index reaches
        // would otherwise never be indexed — the blind spot check_paper_indexes'
        // orphan-module gate fails on. Include them EXCEPT modules a SIBLING
        // development imports: those are the sibling's proof machinery banked
        // into this namespace (e.g. a follow-up paper extending this substrate),
        // and this paper neither uses nor should display them.
        ...(await (async () => {
          const orphans = (
            await findOrphanPaperModules(
              join(io.ctx.repoRoot, io.bank.leanSubdir),
              modPrefix,
              new Set(
                (priorIndex?.entries ?? []).flatMap((e) =>
                  typeof e.module === "string" ? [e.module] : [],
                ),
              ),
            )
          ).map((o) => o.module);
          const foreign = await externallyConsumedModules(
            io.ctx.repoRoot,
            io.bank.leanSubdir,
            new Set(orphans),
          );
          return orphans.filter((m) => !foreign.has(m));
        })()),
      ],
    ),
  ].sort();
  const emitIndex = async (previous: PaperLibraryIndex | null): Promise<PaperLibraryIndex> => {
    const candidatePath = `${indexPath}.next-${process.pid}`;
    try {
      await execFileP(
        "lake",
      // repoRoot IS the CausalSmith package root (findRepoRoot anchors on its
      // lakefile), so it is both the lake dir and the src root.
        ["-d", io.ctx.repoRoot, "exe", "paper_index", "--",
          "--prefix", modPrefix,
          "--src-root", io.ctx.repoRoot,
          // Import the paper modules directly so indexing does not depend on a
          // run being wired into the CausalSmith root import graph.
          "--modules", modTargets.join(","),
          "--out", candidatePath],
        { cwd: io.ctx.repoRoot, maxBuffer: 16 * 1024 * 1024, timeout: 1800_000 },
      );
      const candidate = await readPaperLibraryIndex(candidatePath);
      if (!candidate) throw new Error("P4: paper_index produced no output");
      validatePaperIndexReplacement(previous, candidate, modTargets);
      await rename(candidatePath, indexPath);
      return candidate;
    } catch (err) {
      await rm(candidatePath, { force: true });
      throw err;
    }
  };
  if (modTargets.length === 0)
    throw new Error("P4: no paper modules available for paper_library_index emission");
  await execFileP("lake", ["-d", io.ctx.repoRoot, "build", ...modTargets], {
    cwd: io.ctx.repoRoot,
    maxBuffer: 16 * 1024 * 1024,
    timeout: 1800_000,
  });
  const emittedIndex = await emitIndex(priorIndex);

  // Docstring coverage is authored UPSTREAM (the F5 docstring pass; docstring-canonical
  // workflow) — P4 only verifies it. An undocumented decl would ship as "no translation yet"
  // in the site drawer, so the emit fails with the exact list instead of editing Lean here.
  const undocumented = (emittedIndex.entries ?? []).filter(
    (e) => !e.doc && typeof e.name === "string",
  );
  if (undocumented.length > 0) {
    throw new Error(
      `P4: ${undocumented.length} declaration(s) in the paper's modules lack docstrings — ` +
      undocumented.slice(0, 12).map((e) => `${e.file}:${e.line} ${e.name}`).join(", ") +
      (undocumented.length > 12 ? ` (+${undocumented.length - 12} more)` : "") +
      `. Docstrings are authored at F5 (first paragraph = the NL translation), not at emit; ` +
      `add them to the Lean sources and re-run --from P4.`,
    );
  }

  // Join off the JSON source of truth (explicit obj_id = node id, loaded above), not a re-parse of
  // paper.tex. The paper's assembled envs must still match the source exactly — that is now an
  // equality lint (also catches MISSING envs, which the per-env body compare cannot).
  const layerMismatches = paperEnvMismatches(paperTex, formalLayer.blocks);
  if (layerMismatches.length > 0) {
    throw new Error(`P4: paper.tex disagrees with formal_layer.json: ${layerMismatches.join("; ")}`);
  }
  if (normalizeCitedScopeFootnotes(paperTex, formalLayer.blocks) !== paperTex) {
    throw new Error("P4: generated cited-dependency scope footnote changed during LaTeX repair; rerun from P2");
  }
  // Content (obj_id → lean/title/body) comes from the JSON blocks; the ORDER comes from the paper
  // (env numbering "Theorem 1"/"Assumption 2" follows appearance). parseAnchoredEnvs supplies only
  // the appearance order here — the join key is the explicit block obj_id, never a parsed label.
  const blockByObj = new Map(formalLayer.blocks.filter((b) => b.env).map((b) => [b.obj_id, b] as const));
  const envs = parseAnchoredEnvs(paperTex).flatMap((e, i) => {
    const b = blockByObj.get(e.obj_id);
    return b && b.env ? [{ env: b.env, obj_id: b.obj_id, title: b.title, body: b.body, order: i }] : [];
  });
  // The note's PLT anchors are obj_id aliases (`A-1`/`P-1`/`T-1`); the frozen-layer env labels and
  // the graph-derived crosswalk are keyed by NODE id. Remap each block's alias → node id via the
  // graph so the note-block joins below (fallback text, load-bearing hypotheses, the assumption-
  // table totality gate) line up with the env labels. Blocks with no graph node keep their key.
  const aliasToNodeId = new Map<string, string>();
  for (const n of io.bank.graph.nodes) if (n.obj_id) aliasToNodeId.set(n.obj_id, n.id);
  const blocks = parseNoteBlocks(io.bank.noteMd).map((b) => ({
    ...b,
    obj_id: aliasToNodeId.get(b.obj_id) ?? b.obj_id,
  }));

  // Composite-object mapping (shared with the P1 statement equivalence audit): every
  // definition/assumption env, and any env without a single standalone decl, gets
  // its actual Lean pieces (component decls / theorem hypothesis binders) via
  // codex discovery, content-keyed cached in components_cache.json. By P4 the P1
  // audit has usually already populated the cache, so this is mostly cache hits.
  const { components: componentsMap, moduleDecls } = await ensureComponentsForEnvs({
    envs,
    crosswalk: io.bank.crosswalk,
    repoRoot: io.ctx.repoRoot,
    leanSubdir: io.bank.leanSubdir,
    cachePath: join(io.outDir, "components_cache.json"),
    deps: io.ctx.deps,
    noteBlocks: new Map(blocks.map((b) => [b.obj_id, b.body])),
    // Graph-first: component sets come from the verified graph (own decl + statement-uses
    // neighbours), so multi-decl objects render all pieces without codex discovery.
    graph: io.bank.graph,
  });

  // causalsmith review verdict per object (obj_id alias preferred, node id fallback) so the
  // bundle records the verified status honestly on every entry.
  const verdictByObj = new Map<string, { status: string }>(
    io.bank.graph.nodes.map((n) => [n.id, { status: n.review.status }]),
  );
  for (const block of formalLayer.blocks) {
    if (!verdictByObj.has(block.obj_id)) verdictByObj.set(block.obj_id, { status: block.status });
  }

  const bundle = await buildBundle({
    envs,
    crosswalk: io.bank.crosswalk,
    blocks,
    repoRoot: io.ctx.repoRoot,
    leanSubdir: io.bank.leanSubdir,
    commit,
    components: componentsMap,
    moduleDecls: new Map([...moduleDecls].map(([k, v]) => [k, { file: v.file, line: v.line, kind: v.kind }])),
    verdictByObj,
  });

  // Symbol realizations: surface EVERY `@realizes <sym>` tag as a drawer object whose components are
  // the declarations that jointly realize the symbol (`μ_a`, `e_P`, `τ_P`, …). The DRAFT (P2) links
  // each one inline in the prose via `\leanref{sym:<name>}{<notation>}` — so they are pushed HERE,
  // before the `\leanref` resolution below, so those `sym:` targets resolve. env "symbol" is exempt
  // from the data-objid integrity check (like "auxiliary"); no body block is required.
  const leanDir = join(io.ctx.repoRoot, io.bank.leanSubdir);
  const symbolNames = await discoverRealizedSymbols(leanDir);
  const symbolItems = [] as Awaited<ReturnType<typeof buildSymbolRealizations>>["items"];
  if (symbolNames.length > 0) {
    const clusters = await buildSymbolClusters(leanDir, symbolNames.map((name) => ({ name })));
    const sym = await buildSymbolRealizations({
      clusters,
      repoRoot: io.ctx.repoRoot,
      leanSubdir: io.bank.leanSubdir,
    });
    bundle.crosswalk.entries.push(...sym.entries);
    Object.assign(bundle.snippets.snippets, sym.snippets);
    symbolItems.push(...sym.items);
  }

  // Inline \leanref links: every referenced obj-id MUST resolve to a formal block, a symbol
  // realization, OR a from-note graph node — a dead link is a hard error (no silent broken drawer).
  // From-note objects that are \leanref'd but are NOT formal blocks (prose-only
  // setup/definition/assumption) get their own drawer entry so the inline link opens the verified Lean.
  const leanrefIds = extractLeanrefIds(paperTex);
  const formalBlockIds = new Set(bundle.crosswalk.entries.map((e) => e.obj_id));
  const graphIds = new Set<string>();
  for (const n of io.bank.graph.nodes) {
    graphIds.add(n.id);
    if (n.obj_id) graphIds.add(n.obj_id);
  }
  const unresolved = [...new Set(leanrefIds)].filter(
    (id) => !formalBlockIds.has(id) && !graphIds.has(id),
  );
  if (unresolved.length > 0) {
    throw new Error(
      `P4: ${unresolved.length} \\leanref target(s) resolve to no formal block or graph node: ` +
        `${unresolved.join(", ")}. Fix the obj-id(s) in paper.tex (must match a crosswalk/graph object).`,
    );
  }
  const proseIds = [...new Set(leanrefIds)].filter((id) => !formalBlockIds.has(id));
  if (proseIds.length > 0) {
    const prose = await buildProseEntries({
      objIds: proseIds,
      graph: io.bank.graph,
      crosswalk: io.bank.crosswalk,
      repoRoot: io.ctx.repoRoot,
      leanSubdir: io.bank.leanSubdir,
      moduleDecls: new Map([...moduleDecls].map(([k, v]) => [k, { file: v.file, line: v.line }])),
    });
    bundle.crosswalk.entries.push(...prose.entries);
    Object.assign(bundle.snippets.snippets, prose.snippets);
  }

  // Cited gates are absent from the numbered paper environment layer, but the web formal panel
  // exposes their exact proposition. Give each one a cited-result drawer entry so that panel row
  // still opens the source-matched Lean `def : Prop` rather than becoming a dead target. Cited
  // results are web-only dependency metadata: unlike narrative `prose` entries, they have no
  // paper-body block and must stay distinguishable from ordinary prose in the bundle contract.
  const citedIds = io.bank.graph.nodes
    .filter(isCitedNode)
    .map((n) => n.id)
    .filter((id) => !bundle.crosswalk.entries.some((e) => e.obj_id === id));
  if (citedIds.length > 0) {
    const cited = await buildProseEntries({
      objIds: citedIds,
      graph: io.bank.graph,
      crosswalk: io.bank.crosswalk,
      repoRoot: io.ctx.repoRoot,
      leanSubdir: io.bank.leanSubdir,
      moduleDecls: new Map([...moduleDecls].map(([k, v]) => [k, { file: v.file, line: v.line }])),
      env: "citedv",
    });
    bundle.crosswalk.entries.push(...cited.entries);
    Object.assign(bundle.snippets.snippets, cited.snippets);
  }

  // Auxiliary Lean lemmas (agent-introduced proof helpers): web-only drawer entries so the
  // Formal-layer panel's auxiliary group opens each helper's verified Lean statement. They carry
  // no body block — env "auxiliary" is exempt from the site's data-objid integrity check.
  const auxIds = auxiliaryNodes(io.bank.graph)
    .filter((n) => !(n.lean.decl_name && bundle.matchedSynthDecls.has(n.lean.decl_name)))
    .map((n) => n.id)
    .filter((id) => !bundle.crosswalk.entries.some((e) => e.obj_id === id));
  if (auxIds.length > 0) {
    const aux = await buildProseEntries({
      objIds: auxIds,
      graph: io.bank.graph,
      crosswalk: io.bank.crosswalk,
      repoRoot: io.ctx.repoRoot,
      leanSubdir: io.bank.leanSubdir,
      moduleDecls: new Map([...moduleDecls].map(([k, v]) => [k, { file: v.file, line: v.line }])),
      env: "auxiliary",
    });
    bundle.crosswalk.entries.push(...aux.entries);
    Object.assign(bundle.snippets.snippets, aux.snippets);
  }

  await writeFile(
    join(io.outDir, "presentation_crosswalk.json"),
    JSON.stringify(PresentationCrosswalk.parse(bundle.crosswalk), null, 2) + "\n",
    "utf8",
  );
  await writeFile(
    join(io.outDir, "lean_snippets.json"),
    JSON.stringify(LeanSnippets.parse(bundle.snippets), null, 2) + "\n",
    "utf8",
  );
  // Proof-citation graph over the paper's results (the site's dependency view). Nodes come from the
  // crosswalk just written, so the two files agree on env/label/title by construction; edges come
  // from the assembled paper's proof bodies. Re-run the isolated-lemma gate against the SAME node
  // set the graph is emitted over — the P2 assembly gate ran on the paper alone, and this is the
  // last boundary before the bundle is published.
  const graphNodes: PaperGraphNode[] = bundle.crosswalk.entries.map((e) => ({
    obj_id: e.obj_id,
    env: e.env,
    paper_label: e.paper_label,
    title: e.title,
  }));
  const isolated = lintIsolatedLemmas(paperTex, graphNodes);
  if (isolated.length > 0) {
    throw new Error(`P4 proof-citation graph: ${isolated.map((p) => p.detail).join("; ")}`);
  }
  await writeFile(
    join(io.outDir, "paper_graph.json"),
    JSON.stringify(buildPaperGraph({ tex: paperTex, nodes: graphNodes, commit }), null, 2) + "\n",
    "utf8",
  );
  // The extractor itself can exit successfully with structurally valid but
  // wrong JSON. Run the independent snapshot + HEAD regression lint only after
  // all three cache inputs exist, and make a failure visible to the pipeline.
  const idxLint = await execFileP(
    "npx",
    ["tsx", "bin/check_paper_indexes.ts", "--strict", "--vs", "HEAD", "--bundle", basename(io.outDir)],
    { cwd: join(io.ctx.repoRoot, "tools"), maxBuffer: 16 * 1024 * 1024 },
  );
  // The check warns (stderr) for every git-untracked module it exempts from the orphan gate; on a
  // SUCCESSFUL run those lines would otherwise vanish with the captured buffer. Persist them so
  // the exemption is visible in the run record, not only on a hand-run of the lint.
  const skipped = (idxLint.stderr ?? "").split("\n").filter((l) => l.includes("[paper-index] skipping"));
  if (skipped.length > 0) {
    io.state.notes.push(`P4 paper-index lint: ${skipped.length} git-untracked module(s) exempted from the orphan gate (in-progress work): ${skipped.map((l) => l.slice(l.lastIndexOf(": ") + 2)).join(", ")}`);
  }
  // Web-only "Formal layer" panel: deterministic, complete list of every from-note object
  // (NL + Lean + verified status) straight from the graph — the backstop for inline \leanref.
  // IMPORTANT: this EMITTED shape is `{commit, groups}` (FormalLayer), which is DIFFERENT from the
  // SOURCE `{commit, blocks}` (FormalLayerSource) that P1 writes and P2/P3/P4 read at `formal_layer.json`.
  // It MUST go to a distinct file — writing it back to `formal_layer.json` clobbers the source, so a
  // P4 resume then fails parsing the emitted shape as the source. The web bundle reads this panel from
  // `formal_layer_web.json`.
  const equivalenceStatus = new Map(
    Object.entries(equivalenceCache).flatMap(([id, v]) => v.verdict === "faithful" ? [[id, "matched"] as const] : []),
  );
  const formalLayerWeb = buildFormalLayer(io.bank.graph, io.bank.crosswalk, commit, equivalenceStatus, bundle.matchedSynthDecls);
  if (symbolItems.length > 0) formalLayerWeb.groups.push({ kind: "symbol", items: symbolItems });
  await writeFile(
    join(io.outDir, "formal_layer_web.json"),
    JSON.stringify(FormalLayer.parse(formalLayerWeb), null, 2) + "\n",
    "utf8",
  );
  io.state.notes.push("P4: verification badge basis = source sorry scan; axiom audit deferred (axioms: null)");

  // P1's notation advisories go stale as P3/P5 revisions land: re-check each one
  // against the shipped paper and disclose survivors instead of dropping them.
  try {
    const nrPath = join(io.outDir, "notation_review.json");
    const nr = JSON.parse(await readFile(nrPath, "utf8")) as {
      ok?: boolean; iterations?: number; advisories?: { gate: string; detail: string }[];
    };
    if (nr.advisories && nr.advisories.length > 0) {
      const reconciled = reconcileXrefAdvisories(nr.advisories, paperTex);
      await writeFile(
        nrPath,
        JSON.stringify({ ...nr, advisories: reconciled.map((r) => ({ ...r.advisory, resolved: r.resolved })) }, null, 2) + "\n",
        "utf8",
      );
      const open = reconciled.filter((r) => r.resolved === false);
      if (open.length > 0) {
        io.state.notes.push(
          `P4: ${open.length} P1 notation/xref advisor${open.length === 1 ? "y" : "ies"} still unresolved in the final paper (see notation_review.json)`,
        );
      }
    }
  } catch {
    /* no notation_review.json (dry run / legacy dir) — skip */
  }

  // assumption-faithfulness table (totality is a hard gate)
  const table = assumptionTable(blocks, envs, bundle.snippets.snippets);
  await writeFile(join(io.outDir, "assumption_table.md"), table.md, "utf8");
  if (table.problems.length > 0) {
    throw new Error(`P4 assumption-table totality failed: ${table.problems.join("; ")}`);
  }

  // web fragment
  // The body's symbol→Lean links are authored by P2 as inline `\leanref{sym:…}{…}` (rendered to a
  // clickable span by tex2html); nothing to post-process here.
  const drawerObjIds = new Set(
    bundle.crosswalk.entries
      .filter((e) => e.lean !== null || bundle.snippets.snippets[e.obj_id] !== undefined)
      .map((e) => e.obj_id),
  );
  await writeFile(
    join(io.outDir, "paper_body.html"),
    await tex2html(paperTex, bib, drawerObjIds) + "\n",
    "utf8",
  );

  // meta
  const outline = parseOutline(await readFile(join(io.outDir, "outline.md"), "utf8"));
  // Resolve cleveref object references to their target-derived kind and number, mirroring tex2html.
  // The abstract is shown as-is on the site (no Pandoc pass), so unresolved commands render raw.
  const refLabels = paperReferenceLabels(paperTex);
  const abstract = resolveObjCrefsPlain(
    (paperTex.match(/\\begin\{abstract\}([\s\S]*?)\\end\{abstract\}/)?.[1]?.trim() ?? "").replace(/~\\/g, " \\"),
    refLabels,
  );
  // Short cluster label (shown in the byline and used to group the landing list).
  const area =
    {
      stat: "Stat",
      pid: "Partial ID",
      eid: "Exact ID",
      exp: "Experimentation",
      panel: "Panel",
    }[io.ctx.qid.split("_")[0]] ?? "Others";
  // TL;DR: a 1-2 sentence skim summary shown above the (folded) abstract on the site.
  // Reuse a non-empty prior one (re-runs / hand-edits) rather than regenerate.
  let tldr = "";
  // P5 injects the overall score into meta.json AFTER P4 emits it. Carry a prior
  // score/rationale forward so a `--from P4` re-emit that has not yet re-run P5
  // does not blank the badge; P5 overwrites with the fresh value on its next pass.
  let score: number | null = null;
  let scoreRationale: string | null = null;
  // `created` is the paper's FIRST publication date (drives the site's timeline sort
  // and the flagship tiebreak) — a re-emit must carry it forward, never re-stamp it.
  let created = new Date().toISOString().slice(0, 10);
  try {
    const prev = JSON.parse(await readFile(join(io.outDir, "meta.json"), "utf8"));
    if (typeof prev.tldr === "string" && prev.tldr.trim()) tldr = prev.tldr.trim();
    if (typeof prev.score === "number") score = prev.score;
    if (typeof prev.score_rationale === "string") scoreRationale = prev.score_rationale;
    if (typeof prev.created === "string" && /^\d{4}-\d{2}-\d{2}$/.test(prev.created)) created = prev.created;
  } catch {
    /* no prior meta.json */
  }
  // A stale TL;DR written before the prose contract should be regenerated rather than carried into
  // a fresh P4 bundle. The regenerated text is checked again below.
  if (tldr && lintNegativeContributionFraming(tldr).length > 0) tldr = "";
  if (!tldr && !io.ctx.deps.dryRun) {
    // One-line TL;DR generation — trivial, low effort.
    const { stdout: out } = await io.ctx.deps.runCodex({
      prompt: await presentationPrompt("p4_tldr", { title: outline.title, abstract }),
      cwd: io.ctx.repoRoot,
      reasoningEffort: "low",
      leanLsp: false,
    });
    tldr = (out ?? "").trim().replace(/^["']+|["']+$/g, "").trim();
  }
  const tldrStyle = lintNegativeContributionFraming(tldr);
  if (tldrStyle.length > 0) {
    throw new Error(`P4 TL;DR violates the affirmative prose contract: ${tldrStyle.map((p) => p.detail).join("; ")}`);
  }
  const meta = PaperMeta.parse({
    qid: io.ctx.qid,
    spec: io.ctx.spec,
    title: outline.title,
    tldr,
    abstract,
    area,
    authorship: null,
    created,
    wp_number: null,
    score,
    score_rationale: scoreRationale,
  });
  await writeFile(join(io.outDir, "meta.json"), JSON.stringify(meta, null, 2) + "\n", "utf8");
  // A successful compiler-repair pass may have applied the same mechanical fix
  // to paper.tex and its authored cache. Preserve that synchronized baseline.
  await recordP2Assembly(io.outDir);
}

/** Authored/cache TeX inputs that P2 uses to assemble paper.tex. Repairs must land here as
 * well as in the assembled file, otherwise a later P2 pass resurrects the compiler error. */
async function authoredTexSources(outDir: string): Promise<string> {
  const paths = [join(outDir, "front_matter.tex"), ...(await texFilesUnder(outDir, ["sections", "proofs"]))];
  return paths.join("\n");
}
