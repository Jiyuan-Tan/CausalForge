import { readFile, writeFile, mkdir } from "node:fs/promises";
import { join } from "node:path";
import type { StageIO } from "../pipeline.js";
import { PRESENTATION_PROSE_POLICY_VERSION, presentationPrompt } from "../prompt_io.js";
import { parseOutline, unwrapArtifact, type Outline } from "../stage_util.js";
import {
  lintAnchors,
  stripRedundantEnvLabels,
  normalizeFrozenEnvs,
  parseAnchoredEnvs,
  repairObjRefs,
  lintNegativeContributionFraming,
  lintReferences,
  normalizeCrefs,
  hashEnvBody,
  type AnchoredEnv,
} from "../tex_anchors.js";
import { FormalLayerSource, normalizeCitedScopeFootnotes, texEnvFor } from "../formal_layer.js";
import { assumptionCiteContext } from "../assumption_citations.js";
import {
  sectionRevisionBrief,
  frontMatterRevisionBrief,
  proofRevisionBrief,
} from "../revision_brief.js";
import { symbolProseTargets, normalizeSymbolLeanrefs, promoteSymbolLeanrefs, repairSymbolLeanrefTargets } from "../emit.js";
import { writeJsonAtomic } from "../json_io.js";
import { runProofAudit } from "../audit.js";
import { extractFullDeclSource } from "../lean_extract.js";
import { discoverRealizedSymbols, buildSymbolClusters } from "../../formalization/crosswalk.js";
import type { FormalizationGraph } from "../graph_view.js";

/** Content key for a P2 section cache entry: changes iff a drafting input changes — the section's
 *  objs list (membership AND order), brief, allowed cites, the frozen env bodies it places, or its
 *  revision brief. An outline restructure that moves an env between sections changes the affected
 *  objs lists, so those sections re-draft rather than reuse a stale env placement. */
export function sectionCacheKey(
  name: string, objs: string[], brief: string, allowedKeys: string, envBodies: string[], revBrief: string,
): string {
  return hashEnvBody([name, objs.join(","), brief, allowedKeys, ...envBodies, revBrief].join("§"));
}

/** Keep only notation rows whose control sequences/identifiers occur in this artifact.
 * Unrelated outline-notation edits must not invalidate every expensive proof render. */
export function relevantNotation(notation: string, artifact: string): string {
  const tokens = new Set(artifact.match(/\\[A-Za-z]+|[A-Za-z][A-Za-z0-9_']{1,}/g) ?? []);
  const rows = notation.split("\n").filter((row) => {
    const rowTokens = row.match(/\\[A-Za-z]+|[A-Za-z][A-Za-z0-9_']{1,}/g) ?? [];
    return rowTokens.some((token) => tokens.has(token));
  });
  return rows.length > 0 ? rows.join("\n") : "(no artifact-specific notation rows)";
}

/** Run-local Lean pointer for a paper object, from the graph (node id → decl).
 *  `null` for an object with no run-local decl (statement-only, or an external
 *  reuse decl with `file: null`). The graph carries no line number, so `line: 0`
 *  — the proof renderer locates the decl by name. */
function leanPointer(graph: FormalizationGraph, objId: string): { file: string; decl: string; line: number } | null {
  const n = graph.nodes.find((x) => x.id === objId);
  if (!n || !n.lean.decl_name || !n.lean.file) return null;
  return { file: n.lean.file, decl: n.lean.decl_name, line: 0 };
}

/**
 * P2 — section-by-section body draft (codex, high effort), Lean-faithful appendix proofs
 * (codex + lean-lsp), abstract/intro written last from the finished body.
 * The assembled paper.tex must pass the anchor + frozen-hash lint before the
 * draft checkpoint; a P2 that breaks the frozen layer never reaches the user.
 */
export async function stageP2(io: StageIO): Promise<void> {
  await mkdir(io.outDir, { recursive: true });
  if (io.ctx.deps.dryRun) {
    await writeFile(join(io.outDir, "p2.stub"), "dry-run\n");
    return;
  }
  const outlineRaw = await readFile(join(io.outDir, "outline.md"), "utf8");
  // Source of truth: the JSON formal layer. Envs are assembled MECHANICALLY from the blocks (via
  // texEnvFor — the same helper P1 uses to derive the .tex view), so the frozen statement that
  // reaches paper.tex is byte-identical to the source and the P4 equality lint is exact.
  const layerSrc = FormalLayerSource.parse(
    JSON.parse(await readFile(join(io.outDir, "formal_layer.json"), "utf8")),
  );
  const legacyFormalRefs = layerSrc.blocks.filter((b) => /\\(?:auto|eq)?ref\{/.test(b.body));
  if (legacyFormalRefs.length > 0) {
    throw new Error(
      `P2 requires a P1 cleveref refresh: ${legacyFormalRefs.length} frozen formal object(s) still use legacy \\ref ` +
      `(${legacyFormalRefs.map((b) => b.obj_id).join(", ")}). Re-run from P1 so formal_layer.json remains the source of truth.`,
    );
  }
  const frozen: Record<string, string> = Object.fromEntries(layerSrc.blocks.map((b) => [b.obj_id, b.body_hash]));
  const brief = await readFile(join(io.outDir, "related_work_brief.md"), "utf8");
  const outline = parseOutline(outlineRaw);

  const envBlocks = layerSrc.blocks.filter((b) => b.env);
  const envs: AnchoredEnv[] = envBlocks.map((b, i) => ({
    env: b.env!,
    obj_id: b.obj_id,
    title: b.title,
    body: b.body,
    order: i,
  }));
  const envText = new Map(envBlocks.map((b) => [b.obj_id, texEnvFor(b)]));
  const blockById = new Map(envBlocks.map((b) => [b.obj_id, b] as const));
  const citedDependencyPromptFor = (objId: string): string => {
    const deps = blockById.get(objId)?.cited_dependencies ?? [];
    if (deps.length === 0) return "(none)";
    return deps.map((d) => {
      const cite = d.cite_key ? `\\citep{${d.cite_key}}` : d.cite_id;
      return `- ${cite}${d.locator ? `, ${d.locator}` : ""}: ${d.statement.replace(/\s+/g, " ").trim()} ` +
        `(published source proof not formalized here; invoke it as cited literature, not as an assumption of this paper)`;
    }).join("\n");
  };
  validatePlacement(outline, envs);

  // From-note objects (setup/definition/assumption) the prose may inline-link to their Lean via
  // \leanref. Listed by obj-id so the author uses the exact key the drawer/P4 validation resolves.
  const leanrefObjects = io.bank.graph.nodes
    .filter(
      (n) =>
        n.provenance === "from-note" &&
        (n.kind === "setup" || n.kind === "definition" || n.kind === "assumption"),
    )
    .map(
      (n) =>
        `${n.obj_id ?? n.id} [${n.kind}]: ${(n.nl?.statement ?? "").replace(/\s+/g, " ").slice(0, 140)}`,
    )
    .join("\n");

  // Core symbols realized in Lean (the `@realizes` tags): the draft links each one's NOTATION inline
  // via \leanref{sym:<name>}{<math>} at its first mention, so a reader can click the symbol itself
  // (μ_a, e_P, …) to see how it is realized. Derived from the Lean tags, generic preferred over arms.
  const leanDir = join(io.ctx.repoRoot, io.bank.leanSubdir);
  const symTargets = symbolProseTargets(
    await buildSymbolClusters(leanDir, (await discoverRealizedSymbols(leanDir)).map((name) => ({ name }))),
  );
  const symbolLeanrefTargets =
    symTargets
      .map((t) => `sym:${t.name} [symbol]: ${t.description.replace(/\s+/g, " ").slice(0, 140)}`)
      .join("\n") || "(none)";

  // Assumption citation provenance: the paper's references.bib (P0-curated) is the bib
  // namespace; each standard assumption's discovery cite is reconciled to a paper key (or a
  // fresh entry is injected). Computed per section so the drafter glosses + cites the
  // assumptions IT presents; injections are appended to references.bib once, after drafting.
  const bibPath = join(io.outDir, "references.bib");
  const bibText = await readFile(bibPath, "utf8").catch(() => "");
  const bibInjections = new Map<string, string>(); // dedup by injected key

  // P5 feedback is never fanned back out across section/proof writers. These
  // inert briefs retain the first-draft prompt contract; post-review work is
  // performed only by the holistic reviser.
  const priorReview = null;

  // body sections (abstract/introduction are written last)
  const bodySections = outline.sections.filter((s) => !/^(abstract|introduction)$/i.test(s.name));
  const isAppendixSection = (name: string) => /^appendix\b/i.test(name.trim());
  const sectionTexs: string[] = [];
  const appendixTexs: string[] = [];
  await mkdir(join(io.outDir, "sections"), { recursive: true });
  // Content-keyed section cache: a section is reused only when its DRAFTING INPUTS are unchanged
  // (its objs set, brief, allowed cites, the frozen env bodies it places, and the revision brief).
  // An outline restructure that moves an env between sections changes the affected sections' objs,
  // so they re-draft instead of shipping a stale env placement (which the P4 ref-lint would reject).
  const cacheKeyPath = join(io.outDir, "sections", "_cache_keys.json");
  const cacheKeys: Record<string, string> = JSON.parse(await readFile(cacheKeyPath, "utf8").catch(() => "{}"));
  const modelCacheKey = `${io.ctx.deps.codexModel ?? "unspecified-codex-model"}|${PRESENTATION_PROSE_POLICY_VERSION}`;
  for (let i = 0; i < bodySections.length; i++) {
    const s = bodySections[i];
    const name = `${String(i + 1).padStart(2, "0")}_${s.name.toLowerCase().replace(/[^a-z0-9]+/g, "_")}.tex`;
    // Citation guidance + resolved keys for THIS section's assumptions (computed even when the
    // section is cache-hit, so references.bib still receives the injected entries on a P2 retry).
    const aCtx = assumptionCiteContext(io.bank.graph, s.objs, bibText);
    for (const e of aCtx.injections) {
      const k = e.match(/@\w+\s*\{\s*([^,\s]+)/)?.[1];
      if (k) bibInjections.set(k, e);
    }
    const citedKeys = s.objs.flatMap((id) =>
      (blockById.get(id)?.cited_dependencies ?? []).flatMap((d) => d.cite_key ? [d.cite_key] : []),
    );
    const allowedKeys = [...new Set([...s.bib, ...aCtx.extraKeys, ...citedKeys])].join(", ");
    const citedNotes = s.objs
      .filter((id) => (blockById.get(id)?.cited_dependencies.length ?? 0) > 0)
      .map((id) => `${id}:\n${citedDependencyPromptFor(id)}`)
      .join("\n\n") || "(none)";
    const revBrief = sectionRevisionBrief(priorReview, s.name);
    // Content key: re-draft when any drafting input changes (objs/brief/cites/env bodies/revision).
    const sectionKey = hashEnvBody([modelCacheKey, sectionCacheKey(name, s.objs, s.brief, allowedKeys, s.objs.map((id) => envText.get(id) ?? ""), `${revBrief}\n${citedNotes}`)].join("§"));
    // Artifact cache, content-keyed: an unchanged section is reused (a P2 retry does not re-draft);
    // a changed objs/brief/env-set re-drafts. Delete sections/ to force a full regenerate.
    let tex = cacheKeys[name] === sectionKey ? await readFile(join(io.outDir, "sections", name), "utf8").catch(() => null) : null;
    // A cache predating the global prose contract must not bypass the P2 authoring rule.
    if (tex !== null && lintNegativeContributionFraming(tex).length > 0) tex = null;
    if (tex === null) {
      // Codex drafts the body section; high effort (the main faithful prose, must
      // match the frozen envs + outline and cite only the allowed keys).
      const { stdout: reply } = await io.ctx.deps.runCodex({
        prompt: await presentationPrompt("p2_section", {
          outline: outlineRaw,
          section_brief: `## section: ${s.name}\n${s.brief}`,
          frozen_envs_for_section: s.objs.map((id) => envText.get(id)!).join("\n\n"),
          allowed_bib_keys: allowedKeys,
          assumption_notes: aCtx.notes || "(no assumptions in this section)",
          cited_dependency_notes: citedNotes,
          notation_table: outline.notation,
          // Sections already drafted (for narrative coherence: no repetition,
          // consistent notation/terminology, valid back-references).
          prior_sections: sectionTexs.length > 0 ? sectionTexs.join("\n\n") : "(this is the first section)",
          leanref_objects: leanrefObjects || "(none)",
          symbol_leanref_targets: symbolLeanrefTargets,
          revision_brief: revBrief,
        }),
        cwd: io.ctx.repoRoot,
        reasoningEffort: "high",
        leanLsp: false,
      });
      tex = unwrapArtifact(reply, ["latex", "tex"], "tex");
    }
    tex = stripRedundantEnvLabels(tex);
    // The frozen layer is the trust anchor: mechanically substitute every
    // anchored env with its canonical text (models sometimes paraphrase while
    // "copying exactly"; that must never reach the lint as drift).
    tex = normalizeFrozenEnvs(tex, envText);
    tex = normalizeCitedScopeFootnotes(tex, envBlocks);
    tex = normalizeCrefs(tex);
    const proseStyle = lintNegativeContributionFraming(tex);
    if (proseStyle.length > 0) {
      throw new Error(`P2 section ${s.name} violates the affirmative prose contract: ${proseStyle.map((p) => p.detail).join("; ")}`);
    }
    await writeFile(join(io.outDir, "sections", name), tex + "\n", "utf8");
    cacheKeys[name] = sectionKey;
    // Persist the key with its section: a crash in a LATER section or in the proof
    // loop must not discard this draft's cache entry (a retry would re-pay every
    // high-effort section call — the stated P2-retry-reuse contract).
    await writeJsonAtomic(cacheKeyPath, cacheKeys);
    if (isAppendixSection(s.name)) {
      // Placed after \appendix below, which auto-letters each section (A, B, …). Strip any heading
      // decoration the drafter added that would DOUBLE that letter: an "Appendix:" prefix (→ "A
      // Appendix: …") or a redundant manual "A. "/"B. " letter prefix (→ "A A. …").
      tex = tex
        .replace(/\\section\{\s*Appendix:?\s*/i, "\\section{")
        .replace(/\\section\{\s*[A-Z]\.\s+/, "\\section{");
      appendixTexs.push(tex);
    } else {
      sectionTexs.push(tex);
    }
  }

  // Append the reconciliation injections (standard assumptions whose discovery reference is
  // NOT already in the paper's references.bib under any key) so every \citep resolves. Idempotent:
  // skip any key already present (a re-run, or a paper key reused by reconciliation).
  if (bibInjections.size > 0) {
    const current = await readFile(bibPath, "utf8").catch(() => "");
    const fresh = [...bibInjections].filter(([k]) => !new RegExp(`@\\w+\\s*\\{\\s*${k}\\b`).test(current)).map(([, e]) => e);
    if (fresh.length > 0) {
      await writeFile(
        bibPath,
        current.trimEnd() + "\n\n% --- assumption citation provenance (causalsmith P2) ---\n" + fresh.join("\n\n") + "\n",
        "utf8",
      );
    }
  }

  // Lean-faithful appendix proofs, one per theorem env. Cached per theorem in
  // proofs/<obj_id>.tex (codex renders are the most expensive P2 calls);
  // delete a file to re-render that proof.
  const allLemmaTex = envs.filter((e) => e.env === "lemmav").map((e) => envText.get(e.obj_id)!).join("\n\n");
  const allCitableTex = [...envText.values()].join("\n\n");
  const helperTexFor = (objId: string) => {
    // Graph proof-use edges are extraction hints, not a complete dependency
    // record. Keep the conservative pre-existing citable set in both prompt and
    // key so an omitted-edge helper edit can never reuse a stale rendered proof.
    return envs.find((e) => e.obj_id === objId)?.env === "lemmav" ? allCitableTex : allLemmaTex;
  };
  const theoremProofById = new Map<string, string>(); // for ordering the consolidated proofs section
  await mkdir(join(io.outDir, "proofs"), { recursive: true });
  const proofCacheKeyPath = join(io.outDir, "proofs", "_cache_keys.json");
  const proofCacheKeys: Record<string, string> = JSON.parse(await readFile(proofCacheKeyPath, "utf8").catch(() => "{}"));
  const proofRenderKey = async (
    objId: string,
    envTex: string,
    lean: { file: string; decl: string },
    helperTex: string,
    revisionBrief: string,
  ) => {
    const leanPath = join(io.ctx.repoRoot, io.bank.leanSubdir, lean.file);
    const leanSource = await readFile(leanPath, "utf8").catch(() => "");
    const exactDecl = leanSource
      ? (() => { try { return extractFullDeclSource(leanSource, lean.decl, 0); } catch { return `full-file:${hashEnvBody(leanSource)}`; } })()
      : "";
    const notation = relevantNotation(outline.notation, `${envTex}\n${exactDecl}\n${helperTex}`);
    return hashEnvBody([modelCacheKey, objId, envTex, leanPath, lean.decl, exactDecl, helperTex, notation, revisionBrief, citedDependencyPromptFor(objId), "citation-erasure-v1"].join("§"));
  };
  for (const e of envs.filter((x) => x.env === "theoremv")) {
    const lean = leanPointer(io.bank.graph, e.obj_id);
    if (!lean) continue; // theorem without a run-local Lean decl gets no rendered proof
    const proofPath = join(io.outDir, "proofs", `${e.obj_id}.tex`);
    const helperTex = helperTexFor(e.obj_id);
    const proofBrief = proofRevisionBrief(priorReview, e.obj_id);
    const notation = relevantNotation(outline.notation, `${envText.get(e.obj_id)!}\n${helperTex}`);
    const proofKey = await proofRenderKey(e.obj_id, envText.get(e.obj_id)!, lean, helperTex, proofBrief);
    const cached = proofCacheKeys[e.obj_id] === proofKey ? await readFile(proofPath, "utf8").catch(() => null) : null;
    if (cached !== null) {
      theoremProofById.set(e.obj_id, normalizeCrefs(cached.trim()));
      continue;
    }
    const leanPath = join(io.ctx.repoRoot, io.bank.leanSubdir, lean.file);
    const { stdout } = await io.ctx.deps.runCodex({
      prompt: await presentationPrompt("p2_proof", {
        theorem_env: envText.get(e.obj_id)!,
        lean_proof_source: `file: ${leanPath}\ndeclaration: ${lean.decl}\nRead the file with your tools; do not guess its contents.`,
        helper_lemma_envs: helperTex || "(no paper lemma is a direct dependency)",
        cited_dependencies: citedDependencyPromptFor(e.obj_id),
        notation_table: notation,
        revision_brief: proofBrief,
      }),
      cwd: io.ctx.repoRoot,
      reasoningEffort: "high",
      leanLsp: true,
    });
    if (/^\s*UNCLEAR:/m.test(stdout)) {
      throw new Error(`P2 proof rendering for ${e.obj_id} reported UNCLEAR — see codex output`);
    }
    const proof = normalizeCrefs(stdout.match(/\\begin\{proof\}[\s\S]*?\\end\{proof\}/)?.[0] ?? "");
    if (!proof) throw new Error(`P2: no proof block in codex output for ${e.obj_id}`);
    await writeFile(proofPath, proof + "\n", "utf8");
    proofCacheKeys[e.obj_id] = proofKey;
    // Same crash-safety contract as the section keys: a later UNCLEAR/parse throw
    // must not force a retry to re-render this already-paid proof.
    await writeJsonAtomic(proofCacheKeyPath, proofCacheKeys);
    theoremProofById.set(e.obj_id, proof);
  }

  // Lemma proofs: rendered in BATCHES (cost economy — lemmas are auxiliary),
  // cached per lemma in proofs/<obj_id>.tex exactly like theorem proofs.
  const lemmaProofTexts = await renderLemmaProofBatches(
    io, envs, envText, outline, priorReview, helperTexFor, proofCacheKeys, proofRenderKey,
    citedDependencyPromptFor, proofCacheKeyPath,
  );
  await writeJsonAtomic(proofCacheKeyPath, proofCacheKeys);

  // ── PROOF EQUIVALENCE AUDIT (co-located with proof production). The moment every appendix proof is
  // rendered, reconcile each one's prose against its machine-verified Lean proof — refining drift
  // toward Lean (always safe; the Lean proof type-checks) and rewriting proofs/<id>.tex. A residual
  // unfaithful proof halts P2 (re-render or adjudicate) rather than reaching the draft checkpoint.
  const proofTargets = envs
    .filter((e) => e.env === "theoremv" || e.env === "lemmav")
    .map((e) => ({ e, lean: leanPointer(io.bank.graph, e.obj_id) }))
    .filter((x): x is { e: AnchoredEnv; lean: { file: string; decl: string; line: number } } => x.lean !== null)
    .map(({ e, lean }) => ({ obj_id: e.obj_id, isMain: e.env === "theoremv", lean: { file: lean.file, decl: lean.decl } }));
  const { refined: refinedProofs, problems: proofProblems } = await runProofAudit(io, proofTargets);
  if (proofProblems.length > 0) {
    throw new Error(
      `P2 proof equivalence audit failed (${proofProblems.length} proof(s) still unfaithful after refinement — ` +
        `re-render or adjudicate): ` + proofProblems.map((p) => p.detail).join("; "),
    );
  }
  // Assembly uses the REFINED proofs (override the freshly-rendered maps).
  for (const [id, proof] of refinedProofs) {
    const canonicalProof = normalizeCrefs(proof);
    if (theoremProofById.has(id)) theoremProofById.set(id, canonicalProof);
    if (lemmaProofTexts.has(id)) lemmaProofTexts.set(id, canonicalProof);
  }
  await writeFile(
    join(io.outDir, "appendix_proofs.tex"),
    envs
      .filter((e) => e.env === "theoremv")
      .map((e) => theoremProofById.get(e.obj_id))
      .filter((p): p is string => !!p)
      .join("\n\n") + "\n",
    "utf8",
  );

  // Lemma proof placement follows the outline's statement placement. A lemma whose statement env
  // sits in an APPENDIX section keeps its proof inline (statement → proof). A lemma the outline
  // placed in a BODY section is shown statement-only there, with its proof DEFERRED to the
  // consolidated proofs appendix (mirrors how a body theorem defers its proof) and a forward
  // pointer added after the statement — otherwise the body lemma would print with no proof anywhere.
  const PROOFS_LABEL = "sec:deferred-proofs";
  const bodyObjIds = new Set(outline.sections.filter((s) => !isAppendixSection(s.name)).flatMap((s) => s.objs));
  const bodyLemmaIds = new Set(
    envs
      .filter((e) => e.env === "lemmav" && bodyObjIds.has(e.obj_id) && lemmaProofTexts.has(e.obj_id))
      .map((e) => e.obj_id),
  );

  // Appendix lemmas: proof inline after the statement. Body lemmas: NOT inlined here.
  const appendixWithProofs = appendixTexs.map((tex) => insertLemmaProofs(tex, lemmaProofTexts));
  // Body lemmas: a "proof deferred" pointer after the statement.
  const bodyWithPointers =
    bodyLemmaIds.size > 0 ? sectionTexs.map((tex) => insertProofPointers(tex, bodyLemmaIds, PROOFS_LABEL)) : sectionTexs;
  // Consolidated proofs appendix: main-result theorems + body-placed lemmas, in paper (env) order.
  const proofById = new Map<string, string>([...lemmaProofTexts, ...theoremProofById]);
  const deferredProofs = envs
    .filter((e) => e.env === "theoremv" || (e.env === "lemmav" && bodyLemmaIds.has(e.obj_id)))
    .map((e) => proofById.get(e.obj_id))
    .filter((p): p is string => !!p);

  const body = [
    ...bodyWithPointers,
    // Clear body→appendix separator. After \appendix the article class letters each section (A, B,
    // …) but prints no "Appendix" word, and tex2html strips \appendix entirely on the web — so without
    // this heading neither output marks where the main body ends. \section* is unnumbered (does not
    // consume the appendix letter counter) and passes through pandoc as an <h1> divider on the web.
    "\\appendix",
    "\\section*{Appendices}",
    ...appendixWithProofs,
    ...(deferredProofs.length > 0
      ? [`\\section{Proofs of the main results}\\label{${PROOFS_LABEL}}`, deferredProofs.join("\n\n")]
      : []),
    "\\bibliographystyle{plainnat}",
    "\\bibliography{references}",
  ].join("\n\n");

  // Front matter is a summary of the finished body — content-key it on the body + its revision brief
  // so a re-drafted/restructured body (or a referee front-matter finding) regenerates the abstract/intro.
  const frontBrief = frontMatterRevisionBrief(priorReview);
  const frontKey = hashEnvBody([modelCacheKey, body, frontBrief, brief].join("§")); // why: front-matter prompt includes related_work_brief and output depends on the authoring model.
  let front = cacheKeys["_front"] === frontKey ? await readFile(join(io.outDir, "front_matter.tex"), "utf8").catch(() => null) : null;
  if (front !== null && lintNegativeContributionFraming(front).length > 0) front = null;
  if (front === null) {
    // Intro + abstract: medium effort (summarization of the already-drafted body).
    front = unwrapArtifact(
      (
        await io.ctx.deps.runCodex({
          prompt: await presentationPrompt("p2_intro_abstract", {
            full_body_tex: body,
            related_work_brief: brief,
            revision_brief: frontBrief,
          }),
          cwd: io.ctx.repoRoot,
          reasoningEffort: "medium",
          leanLsp: false,
        })
      ).stdout,
      ["latex", "tex"],
      "tex",
    );
    front = normalizeCrefs(front);
    const proseStyle = lintNegativeContributionFraming(front);
    if (proseStyle.length > 0) {
      throw new Error(`P2 abstract/introduction violates the affirmative prose contract: ${proseStyle.map((p) => p.detail).join("; ")}`);
    }
    await writeFile(join(io.outDir, "front_matter.tex"), front + "\n", "utf8");
  }
  cacheKeys["_front"] = frontKey;
  await writeJsonAtomic(cacheKeyPath, cacheKeys);

  const macros = await readFile(join(import.meta.dirname, "..", "templates", "paper_macros.tex"), "utf8");
  await writeFile(join(io.outDir, "paper_macros.tex"), macros, "utf8");
  const paper = [
    "\\documentclass[11pt]{article}",
    "\\usepackage[margin=1.1in]{geometry}",
    "\\usepackage{amssymb,mathtools,natbib}",
    "\\input{paper_macros.tex}",
    `\\title{${outline.title}}`,
    "\\author{CausalSmith\\thanks{Machine-generated and Lean-verified by the CausalSmith research pipeline.}}",
    "\\date{\\today}",
    "\\begin{document}",
    "\\maketitle",
    front,
    body,
    "\\end{document}",
  ].join("\n\n");
  // Make every symbol `\leanref{sym:…}{…}` math-mode-safe (`\ensuremath`) so a display the drafter put
  // inside a `\(…\)` (a `$…$` nested in `\(…\)` is a fatal TeX error) still compiles at P4; then PROMOTE
  // any symbol link that leads a `\(…\)` to standalone, so the symbol stays clickable on the web instead
  // of being stripped to bare math (the drafter often writes the first mention as `\(\leanref…=…\)`).
  const paperNorm = promoteSymbolLeanrefs(normalizeSymbolLeanrefs(repairSymbolLeanrefTargets(paper, symTargets.map((t) => t.name))));
  // Repair cleveref object ids (proof bodies sometimes drop a kind prefix → silent "??") against
  // the labels the paper actually defines; a residual dangling ref fails the stage loud.
  const definedIds = new Set(parseAnchoredEnvs(paperNorm).map((e) => e.obj_id));
  const { tex: paperSafe, problems: refProblems } = repairObjRefs(paperNorm, definedIds);

  // The formal layer is the paper's complete environment namespace. It includes graph-backed
  // objects plus P1's presentation-owned setup definitions; only the former require crosswalk/Lean
  // anchors, but both are valid frozen env ids for the P2 anchor lint.
  const known = new Set(layerSrc.blocks.map((b) => b.obj_id));
  const problems = [
    ...lintAnchors(paperSafe, known, new Map(Object.entries(frozen))),
    ...lintReferences(paperSafe),
    ...refProblems,
  ];
  if (problems.length > 0) {
    throw new Error(
      `P2 paper lint failed: ${problems.map((p) => `${p.gate}: ${p.detail}`).join("; ")}`,
    );
  }
  await writeFile(join(io.outDir, "paper.tex"), paperSafe + "\n", "utf8");
}

const LEMMA_BATCH = 5;

/** Splits batched codex output on `%% PROOF <obj_id>` markers into per-lemma
 *  proof blocks. Exported for tests. */
export function parseLemmaProofBatch(stdout: string, expected: string[]): Map<string, string> {
  const out = new Map<string, string>();
  const re = /^%% PROOF ([\w:-]+)\s*$/gm; // obj_ids are node ids → may contain ':' (prop:overlap-envelope)
  const marks: { id: string; start: number; end: number }[] = [];
  for (let m = re.exec(stdout); m; m = re.exec(stdout)) {
    marks.push({ id: m[1], start: m.index, end: m.index + m[0].length });
  }
  for (let i = 0; i < marks.length; i++) {
    const chunk = stdout.slice(marks[i].end, i + 1 < marks.length ? marks[i + 1].start : undefined);
    const block =
      chunk.match(/\\begin\{proof\}[\s\S]*?\\end\{proof\}/)?.[0] ??
      (/^\s*UNCLEAR:/m.test(chunk) ? chunk.match(/^\s*UNCLEAR:.*$/m)![0].trim() : null);
    if (block) out.set(marks[i].id, block);
  }
  const missing = expected.filter((id) => !out.has(id));
  if (missing.length > 0) {
    throw new Error(`P2 lemma proof batch: no parseable proof for ${missing.join(", ")}`);
  }
  return out;
}

/** Renders proofs for all lemmav envs with a Lean mapping, batched (cost
 *  economy), cached per lemma in proofs/<obj_id>.tex. Returns obj_id → proof. */
async function renderLemmaProofBatches(
  io: StageIO,
  envs: AnchoredEnv[],
  envText: Map<string, string>,
  outline: Outline,
  priorReview: null,
  helperTexFor: (objId: string) => string,
  proofCacheKeys: Record<string, string>,
  proofRenderKey: (
    objId: string,
    envTex: string,
    lean: { file: string; decl: string },
    helperTex: string,
    revisionBrief: string,
  ) => Promise<string>,
  citedDependencyPromptFor: (objId: string) => string,
  proofCacheKeyPath: string,
): Promise<Map<string, string>> {
  const out = new Map<string, string>();
  const pending: { e: AnchoredEnv; lean: { file: string; decl: string; line: number } }[] = [];
  for (const e of envs.filter((x) => x.env === "lemmav")) {
    const lean = leanPointer(io.bank.graph, e.obj_id);
    if (!lean) continue; // statement-only lemma (no run-local Lean decl) gets no proof
    const proofKey = await proofRenderKey(
      e.obj_id, envText.get(e.obj_id)!, lean, helperTexFor(e.obj_id), proofRevisionBrief(priorReview, e.obj_id),
    );
    const cached = proofCacheKeys[e.obj_id] === proofKey ? await readFile(join(io.outDir, "proofs", `${e.obj_id}.tex`), "utf8").catch(() => null) : null;
    if (cached !== null) {
      out.set(e.obj_id, cached.trim());
      continue;
    }
    pending.push({ e, lean });
  }
  for (let i = 0; i < pending.length; i += LEMMA_BATCH) {
    const batch = pending.slice(i, i + LEMMA_BATCH);
    const citable = [...new Set(batch.map(({ e }) => helperTexFor(e.obj_id)).filter(Boolean))].join("\n\n");
    const block = batch
      .map(({ e, lean }, j) => {
        const leanPath = join(io.ctx.repoRoot, io.bank.leanSubdir, lean.file);
        const cited = citedDependencyPromptFor(e.obj_id);
        return `### Lemma ${j + 1} — obj_id ${e.obj_id}\n${envText.get(e.obj_id)!}\nLean proof: file ${leanPath}, declaration ${lean.decl}. Read the file with your tools; do not guess its contents.\nPublished cited dependencies:\n${cited}\nRevision brief for this lemma:\n${proofRevisionBrief(priorReview, e.obj_id)}`;
      })
      .join("\n\n");
    const { stdout } = await io.ctx.deps.runCodex({
      prompt: await presentationPrompt("p2_lemma_proofs_batch", {
        lemmas_block: block,
        citable_envs: citable,
        notation_table: relevantNotation(outline.notation, `${block}\n${citable}`),
        revision_brief: "(each lemma carries its own object-scoped brief above)",
      }),
      cwd: io.ctx.repoRoot,
      reasoningEffort: "high",
      leanLsp: true,
    });
    const parsed = parseLemmaProofBatch(stdout, batch.map(({ e }) => e.obj_id));
    for (const [id, rawProof] of parsed) {
      const proof = normalizeCrefs(rawProof);
      if (/^\s*UNCLEAR:/.test(proof)) {
        throw new Error(`P2 lemma proof for ${id} reported UNCLEAR — see codex output`);
      }
      await writeFile(join(io.outDir, "proofs", `${id}.tex`), proof + "\n", "utf8");
      proofCacheKeys[id] = await proofRenderKey(
        id,
        envText.get(id)!,
        batch.find(({ e }) => e.obj_id === id)!.lean,
        helperTexFor(id),
        proofRevisionBrief(priorReview, id),
      );
      out.set(id, proof);
    }
    // Persist per batch: a parse failure in a LATER batch must not discard the
    // cache keys of the proofs this batch already rendered and wrote.
    await writeJsonAtomic(proofCacheKeyPath, proofCacheKeys);
  }
  return out;
}

/** Inserts each lemma proof directly after its \end{lemmav} block. Exported
 *  for tests. */
export function insertLemmaProofs(tex: string, proofs: Map<string, string>): string {
  return tex.replace(
    /\\begin\{lemmav\}\{([\w:-]+)\}(\[[^\]]*\])?[\s\S]*?\\end\{lemmav\}/g, // obj_id may contain ':'
    (envBlock, objId: string) => {
      const proof = proofs.get(objId);
      return proof ? `${envBlock}\n\n${proof}` : envBlock;
    },
  );
}

/** Appends a "proof deferred" pointer after each BODY lemma's \end{lemmav} block (for the ids in
 *  `lemmaIds`, whose proofs live in the consolidated proofs appendix labelled `sectionLabel`).
 *  Without it a body-placed lemma would print statement-only, with its proof nowhere. Exported
 *  for tests. */
export function insertProofPointers(tex: string, lemmaIds: Set<string>, sectionLabel: string): string {
  return tex.replace(
    /\\begin\{lemmav\}\{([\w:-]+)\}(\[[^\]]*\])?[\s\S]*?\\end\{lemmav\}/g,
    (envBlock, objId: string) =>
      lemmaIds.has(objId)
        ? `${envBlock}\n\nThe proof is deferred to \\cref{${sectionLabel}}.`
        : envBlock,
  );
}

function validatePlacement(outline: Outline, envs: AnchoredEnv[]): void {
  const placed = outline.sections.flatMap((s) => s.objs);
  const placedSet = new Set(placed);
  const envIds = new Set(envs.map((e) => e.obj_id));
  const missing = [...envIds].filter((id) => !placedSet.has(id));
  const unknown = placed.filter((id) => !envIds.has(id));
  const dupes = placed.filter((id, i) => placed.indexOf(id) !== i);
  if (missing.length || unknown.length || dupes.length) {
    throw new Error(
      `P2 outline placement invalid — missing: [${missing.join(", ")}], unknown: [${unknown.join(", ")}], duplicated: [${dupes.join(", ")}]`,
    );
  }
}
