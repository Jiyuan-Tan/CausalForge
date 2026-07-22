import { readFile, writeFile, mkdir } from "node:fs/promises";
import { join } from "node:path";
import type { StageIO } from "../pipeline.js";
import { PRESENTATION_PROSE_POLICY_VERSION, presentationPrompt } from "../prompt_io.js";
import { parseOutline, unwrapArtifact } from "../stage_util.js";
import {
  lintAnchors,
  lintClarity,
  lintSelfContainment,
  lintCrossRefs,
  lintReferences,
  normalizeCrefs,
  lintHypothesisPresentation,
  orphanParameterizedClasses,
  hashEnvBody,
  parseAnchoredEnvs,
  containsNotation,
  sameEstimatorNotationFamily,
  type LintProblem,
} from "../tex_anchors.js";
import { parseBib } from "../citations.js";
import { parseJsonLoose, mapLimit } from "../gates.js";
import { buildLeanContextIndex, type LeanContext } from "../lean_context.js";
import { citedDependencies, renderedNodes, topoOrder, refTargets, envForNode, isCitedNode } from "../graph_view.js";
import { citedStdFromNode, reconcileCite, indexBib } from "../assumption_citations.js";
import { outlineRevisionBrief } from "../revision_brief.js";
import { blocksFromGraph, blocksToTex, FormalLayerSource, hashBody, type FormalBlock } from "../formal_layer.js";
import {
  runP1Loop,
  renderMechanicalLayer,
  type P1Env,
  type P1Finding,
  type P1LoopHooks,
} from "../p1_loop.js";
import { runStatementAudit } from "../audit.js";
import { writeJsonAtomic } from "../json_io.js";
import {
  discoverRealizedSymbols,
  buildRealizedNotationMatcher,
} from "../../formalization/crosswalk.js";

const OPEN_DIRECTION_RE = /\b(?:open (?:question|problem|direction)|unresolved (?:question|issue)|remains? (?:open|unknown|unresolved)|remain(?:s)? to (?:be )?(?:shown|determined|understood|resolved)|ask(?:s|ed)? whether|question (?:is|of) whether|future work|further work|future research|next step|worth (?:investigating|studying)|natural (?:question|direction|extension|strengthening))\b/i;
const ASSERTED_RESULT_RE = /\b(?:(?:we|this (?:paper|work)|our (?:paper|work|result|analysis))\s+(?:prove|proves|establish|establishes|show|shows|derive|derives|demonstrate|demonstrates)|(?:theorem|corollary|proposition|our result)\b[^.!?]{0,100}\b(?:prove|proves|establish|establishes|show|shows|imply|implies)|it follows that|we conclude that|is established here|has been proved)\b/i;
const ASSERTIVE_REVERSAL_RE = /\b(?:nevertheless|in fact|indeed|therefore|thus|hence)\b/i;
const LEGALISTIC_UNDELIVERED_RE = /^\s*this work does not (?:establish|prove|deliver)/i;

/** A model-written remark is acceptable only when it clearly frames the claim as an open
 * direction and does not turn around and assert it as a theorem/result. */
export function safelyFramesUndeliveredRemark(body: string): boolean {
  const text = body.trim();
  return text.length > 0 && OPEN_DIRECTION_RE.test(text) && !ASSERTED_RESULT_RE.test(text) && !ASSERTIVE_REVERSAL_RE.test(text) && !LEGALISTIC_UNDELIVERED_RE.test(text);
}

/** Boundary parse of the P1 notation-reviewer reply. An unusable reply must throw,
 *  not collapse to a clean review: this path previously defaulted to `[]`, so a
 *  reviewer that answered in prose silently passed the notation gate. */
export function parseNotationReviewerOutput(
  stdout: string,
): { symbol?: string; used_in?: string[]; case?: string; fix?: string }[] {
  const parsed = parseJsonLoose(stdout) as { clean?: unknown; problems?: unknown } | null;
  if (parsed === null) {
    throw new Error("P1 notation reviewer output is not parseable JSON — re-run P1 (inputs are cached)");
  }
  if (Array.isArray(parsed.problems)) {
    return parsed.problems as { symbol?: string; used_in?: string[]; case?: string; fix?: string }[];
  }
  if (parsed.clean === true) return [];
  throw new Error("P1 notation reviewer output has neither clean:true nor a problems array — re-run P1");
}

/** Reader-facing rendering of a node this run explicitly does not deliver. The agent normally
 * supplies varied prose; deterministic variants are only the fail-closed fallback for an unsafe
 * or missing render. Previously frozen theorem bodies never cross this boundary. */
export function undeliveredRemarkBody(statement: string, reason: string, candidate?: string): string {
  if (candidate && safelyFramesUndeliveredRemark(candidate)) return candidate.trim();
  const claim = statement.trim().replace(/\s+/g, " ");
  const why = reason.trim().replace(/^[a-z0-9-]+:\s*/i, "").replace(/\s+/g, " ");
  const variants = [
    `A natural open question is whether the following proposed conclusion holds: \\emph{${claim}}. Addressing it would require ${why}, and we leave it for future work.`,
    `It remains open in the present framework whether \\emph{${claim}}. The missing ingredient is ${why}; resolving it is a direction for further work.`,
    `One worthwhile direction for future research is to determine whether \\emph{${claim}}. Doing so requires ${why}, which lies beyond the present development.`,
  ];
  const variant = [...claim].reduce((sum, ch) => sum + ch.codePointAt(0)!, 0) % variants.length;
  return variants[variant];
}

/** Select the final JSON/TeX body without letting a stale theorem freeze override a newly
 * undelivered remark. Kept pure so the final-emission boundary has direct regression coverage. */
export function presentedBody(
  deliveryStatus: string | undefined,
  frozenBody: string | undefined,
  loopBody: string | undefined,
): string {
  return deliveryStatus === "undelivered" ? (loopBody ?? "") : (frozenBody ?? loopBody ?? "");
}

/** Outline must place every frozen env exactly once and cite only pool keys. */
function validateOutline(outlineMd: string, ids: string[], poolKeys: Set<string>): string[] {
  const problems: string[] = [];
  const outline = parseOutline(outlineMd);
  if (!outlineMd.trimStart().startsWith("# Title")) {
    problems.push("outline does not start with `# Title` — output-format drift");
  }
  if (outline.sections.length < 3) problems.push(`only ${outline.sections.length} sections parsed`);
  const placed = outline.sections.flatMap((s) => s.objs);
  for (const id of ids) {
    const n = placed.filter((p) => p === id).length;
    if (n !== 1) problems.push(`obj ${id} placed ${n} times (must be exactly 1)`);
  }
  for (const extra of placed.filter((p) => !ids.includes(p) && !/^synth_\d+$/.test(p))) {
    problems.push(`obj ${extra} is not in the frozen layer`);
  }
  for (const key of new Set(outline.sections.flatMap((s) => s.bib))) {
    if (!poolKeys.has(key)) problems.push(`bib key ${key} is not in the citation pool`);
  }
  return problems;
}

/** Place presentation-synthesized setup definitions in the paper outline. They are not graph
 * theorem nodes, but P2 still requires every formal-layer environment to be assigned exactly once. */
export function placeSynthesizedDefinitions(outlineMd: string, ids: string[]): string {
  const lines = outlineMd.split("\n");
  let sectionStart = lines.findIndex((line) => /^## section:.*(?:setup|assumption)/i.test(line));
  if (sectionStart < 0) sectionStart = lines.findIndex((line) => /^## section:/.test(line));
  if (sectionStart < 0) throw new Error("P1 cannot place synthesized definitions: outline has no section");
  const nextSection = lines.findIndex((line, i) => i > sectionStart && /^## section:/.test(line));
  const sectionEnd = nextSection < 0 ? lines.length : nextSection;
  const objsLine = lines.findIndex((line, i) => i > sectionStart && i < sectionEnd && /^objs:\s*/.test(line));
  if (objsLine < 0) throw new Error("P1 cannot place synthesized definitions: target section has no objs line");
  const existingRaw = lines[objsLine].replace(/^objs:\s*/, "").trim();
  const existing = /^(?:none|\(none\))$/i.test(existingRaw)
    ? []
    : existingRaw.split(",").map((x) => x.trim()).filter((x) => x && !/^synth_\d+$/.test(x));
  lines[objsLine] = `objs: ${[...new Set([...ids, ...existing])].join(", ")}`;
  return lines.join("\n");
}

/** Convert a deterministic LintProblem to a loop finding (gate/objId/detail carry over). */
const toFinding = (p: LintProblem): P1Finding => ({ gate: p.gate, objId: p.objId, detail: p.detail });

/**
 * P1 — paper plan + frozen formal layer, as the executor→reviewer→router loop
 * (design §4.6). Statements come from the graph (`nl.statement`); the codex
 * executor renders them to paper prose; the codex reviewer + deterministic floor
 * check readability / self-containment / notation; the router re-renders, or
 * synthesizes a missing class, or halts. Frozen bodies are then hash-pinned and
 * the dispatcher halts at the outline checkpoint.
 */
export async function stageP1(io: StageIO): Promise<void> {
  await mkdir(io.outDir, { recursive: true });
  if (io.ctx.deps.dryRun) {
    await writeFile(join(io.outDir, "p1.stub"), "dry-run\n");
    return;
  }
  const { deps, repoRoot } = io.ctx;
  const graph = io.bank.graph;
  const nodes = topoOrder(graph, renderedNodes(graph));
  if (nodes.length === 0) throw new Error("P1: graph has no frozen paper-env nodes to render");
  const nodeIds = nodes.map((n) => n.id);
  const refTargetsById = new Map(
    nodes.map((n) => [n.id, new Set(refTargets(graph, n.id).map((t) => t.id))]),
  );
  const citedDepsById = new Map(nodes.map((n) => [n.id, citedDependencies(graph, n.id)] as const));
  const citedPromptFor = (id: string): string => {
    const deps = citedDepsById.get(id) ?? [];
    if (deps.length === 0) return "(none — do not erase any Lean hypothesis)";
    return deps.map((d) =>
      `- ${d.lean.decl_name ?? d.id}: ${d.nl.statement.replace(/\s+/g, " ").trim()} ` +
      `[source ${d.gate?.source ?? "missing"}; source-matched status ${d.review.status}]`,
    ).join("\n");
  };

  const brief = await readFile(join(io.outDir, "related_work_brief.md"), "utf8");
  const bibText = await readFile(join(io.outDir, "references.bib"), "utf8");
  const poolKeys = new Set(parseBib(bibText).map((e) => e.key));
  // Inline-citation key per CITED node: reconcile its `gate.source` slug to the P0-curated
  // bib key (surname ⊂ author AND equal year) so the touch-up render attributes the imported
  // result with `\citet{<key>}` rather than hardcoded author-year text. Graph-only, match-only:
  // a slug with no confident bib match is simply omitted (the render falls back to plain prose).
  const bibIndex = indexBib(bibText);
  const citeKeyById = new Map<string, string>();
  for (const n of graph.nodes) {
    if (!isCitedNode(n)) continue;
    const std = citedStdFromNode(n);
    if (!std) continue;
    const { citeKey } = reconcileCite(std, bibIndex);
    if (poolKeys.has(citeKey)) citeKeyById.set(n.id, citeKey);
  }
  const locatorById = new Map<string, string>();
  const passedCitedChecks = new Set<string>();
  for (const check of io.bank.citedChecks ?? []) {
    if (check.locator && !locatorById.has(check.name)) locatorById.set(check.name, check.locator);
    if (["cited-verified", "cited-verified-attested"].includes(check.check_status)) {
      passedCitedChecks.add(check.name);
    }
  }
  const usedCited = [...new Map(
    [...citedDepsById.values()].flat().map((n) => [n.id, n] as const),
  ).values()];
  const unsafeCited = usedCited.filter((n) => !passedCitedChecks.has(n.id) || !citeKeyById.has(n.id));
  if (unsafeCited.length > 0) {
    throw new Error(
      "P1 citation erasure refused: each hidden cited premise needs a persisted verified/attested " +
      "source-match and a resolvable references.bib key — " +
      unsafeCited.map((n) => `${n.id} (check=${passedCitedChecks.has(n.id)}, bib=${citeKeyById.has(n.id)})`).join(", "),
    );
  }

  // P5 revision is owned by the single holistic reviser. P1 is initial planning
  // only and must not independently reinterpret a prior referee report.
  const priorReview = null;
  const outlineBrief = outlineRevisionBrief(priorReview);
  const hasOutlineRevision = priorReview !== null && /^\s*-\s*\[/m.test(outlineBrief);

  const t0 = Date.now();
  const log = (m: string) => console.error(`[causalsmith P1] +${Math.round((Date.now() - t0) / 1000)}s ${m}`);
  log(`graph: ${nodes.length} frozen paper-env nodes → ${nodeIds.join(", ")}`);

  // Content-keyed cache (cost economy — a re-run only re-pays for changed inputs,
  // mirroring the old equivalence/gate caches). `render`: keyed by the touch-up
  // input (statement + refs + prior body + defects) → {title, body}. `notation`:
  // keyed by the layer hash → the codex notation findings. Delete the file to force
  // a full re-render.
  const cachePath = join(io.outDir, "p1_cache.json");
  type RenderHit = { title?: string; body: string };
  const cache: {
    render: Record<string, RenderHit>;
    notation: Record<string, P1Finding[]>;
    outlineKey?: string;
    outlineStructureKey?: string;
    outlineModel?: string;
  } = {
    render: {},
    notation: {},
    ...(JSON.parse(await readFile(cachePath, "utf8").catch(() => "{}")) as object),
  };
  const saveCache = () => writeJsonAtomic(cachePath, cache); // why: a crash mid-write must not corrupt the render cache (next run would throw on parse).
  const modelCacheKey = `${io.ctx.deps.codexModel ?? "unspecified-codex-model"}|${PRESENTATION_PROSE_POLICY_VERSION}`;
  const renderKey = (r: { id: string; statement: string; refSet: string[]; priorBody?: string; defects?: string[]; delivery?: P1Env["delivery"] }) =>
    hashEnvBody([
      modelCacheKey,
      r.statement,
      [...r.refSet].sort().join(","),
      r.priorBody ?? "",
      (r.defects ?? []).join("|"),
      JSON.stringify(r.delivery ?? null),
      citedPromptFor(r.id),
      r.delivery?.status === "undelivered" ? "undelivered-open-direction-v2" : "",
    ].join("§"));

  // ── Outline (executor / codex): structure + notation table over the mechanical layer.
  // Cache by presence (like sections/ and the proof caches): a valid existing outline.md is REUSED.
  // The outline is non-deterministic across codex calls, so a re-run — `--from P1` after a graph fix,
  // or a re-draft incorporating a P5 review — must NOT silently RESTRUCTURE the paper. `validateOutline`
  // guards staleness: if the env set changed since the outline was written, an env is no longer placed
  // exactly once → it fails → we regenerate. Delete outline.md to force a fresh structure.
  const mechanical = renderMechanicalLayer(nodes);
  const outlineKey = hashEnvBody([modelCacheKey, mechanical, [...poolKeys].sort().join(","), brief, outlineBrief].join("§")); // why: a valid outline can still be stale for changed bodies/notation inputs or a changed authoring model.
  const outlineStructureKey = hashEnvBody([
    modelCacheKey,
    nodes.map((n) => `${n.id}:${n.kind}`).join(","),
    [...poolKeys].sort().join(","),
    brief,
    outlineBrief,
  ].join("§"));
  const existingOutline = (await readFile(join(io.outDir, "outline.md"), "utf8").catch(() => "")).trim();
  let outlineMd: string;
  const outlineCacheMatches = cache.outlineStructureKey
    ? cache.outlineStructureKey === outlineStructureKey
    : cache.outlineKey != null && (cache.outlineModel == null || cache.outlineModel === modelCacheKey);
  if (existingOutline && outlineCacheMatches && validateOutline(existingOutline, nodeIds, poolKeys).length === 0) {
    outlineMd = existingOutline;
    cache.outlineStructureKey = outlineStructureKey;
    cache.outlineModel = modelCacheKey;
    await saveCache();
    log("outline: reusing existing valid outline.md (no restructure on re-run)");
  } else {
    log(
      `outline: calling codex…${
        hasOutlineRevision
          ? " (regenerating to apply the P5 structural revision brief)"
          : existingOutline
            ? " (existing outline invalid for current env set — regenerating)"
            : ""
      }`,
    );
    const baseOutlinePrompt = await presentationPrompt("p1_plan", {
        note_md: io.bank.noteMd,
        related_work_brief: brief,
        frozen_layer_tex: mechanical,
        pool_keys: [...poolKeys].join(", "),
        revision_brief: outlineBrief,
        // why: reruns with a valid existing outline must preserve structure unless a structural P5 brief requested movement.
        prior_outline: existingOutline || "(first draft — no prior structure to preserve)",
      });
    let outlineProblems: string[] = [];
    outlineMd = "";
    for (let attempt = 0; attempt < 2; attempt++) {
      const repair = attempt === 0 ? "" : [
        "\n\nREPAIR THE PREVIOUS OUTLINE. The deterministic validator rejected it for:",
        ...outlineProblems.map((p) => `- ${p}`),
        "Return a complete replacement outline. In particular, every `bib:` key must be copied verbatim from the verified pool above; keys mentioned in the note or related-work brief but absent from that pool do not exist.",
        "\nPrevious rejected outline:\n",
        outlineMd,
      ].join("\n");
      const outlineRes = await deps.runCodex({
        prompt: baseOutlinePrompt + repair,
        cwd: repoRoot,
        reasoningEffort: "medium",
        leanLsp: false,
      });
      outlineMd = unwrapArtifact(outlineRes.stdout, ["markdown", "md"], "outline_md");
      outlineProblems = validateOutline(outlineMd, nodeIds, poolKeys);
      if (outlineProblems.length === 0) break;
      await writeFile(join(io.outDir, "outline_rejected.md"), outlineMd + "\n", "utf8");
      log(`outline: rejected attempt ${attempt + 1}/2 — ${outlineProblems.join("; ")}`);
    }
    if (outlineProblems.length > 0) {
      throw new Error(`P1 outline invalid after repair: ${outlineProblems.join("; ")}`);
    }
    await writeFile(join(io.outDir, "outline.md"), outlineMd + "\n", "utf8");
    cache.outlineKey = outlineKey;
    cache.outlineStructureKey = outlineStructureKey;
    cache.outlineModel = modelCacheKey;
    await saveCache();
    log("outline: ok");
  }
  const notation = parseOutline(outlineMd).notation;
  const leanDir = join(repoRoot, io.bank.leanSubdir);
  const realizedSymbols = await discoverRealizedSymbols(leanDir);
  const isLeanRealizedNotation = buildRealizedNotationMatcher(realizedSymbols);
  if (realizedSymbols.length > 0) {
    log(`notation: ${realizedSymbols.length} Lean-realized symbol(s) available as authoritative homes`);
  }

  // ── Loop hooks (the model calls runP1Loop orchestrates).
  // Titles are carried in a side-map (the render emits them; the loop tracks only
  // bodies). A titled definition env lets notation resolution match a class.
  const titleById = new Map<string, string>();
  const notationSymbols = notation.split("\n").flatMap((line) => {
    const cells = line.split("|").map((x) => x.trim()).filter(Boolean);
    if (cells.length < 4) return [];
    const symbol = cells[1].replace(/^\$|\$$/g, "").replace(/^\\\(|\\\)$/g, "").trim();
    return symbol && !/^[A-Za-z]$/.test(symbol) ? [symbol] : [];
  });
  /** Stable topological order induced by notation definitions. This lets a synthetic definition
   * live after the graph objects it depends on (for example theta-star) but before its consumers,
   * instead of forcing every synthetic setup block to the very front or very back. */
  const orderByNotationDefinitions = (envs: P1Env[]): P1Env[] => {
    const byId = new Map(envs.map((e) => [e.id, e]));
    const originalPos = new Map(envs.map((e, i) => [e.id, i]));
    const outgoing = new Map(envs.map((e) => [e.id, new Set<string>()]));
    const indegree = new Map(envs.map((e) => [e.id, 0]));
    for (const symbol of notationSymbols) {
      // Titles are the reliable primary-object signal. A body can mention many symbols in
      // equations (`theta*` inside the definition of an energy denominator); treating every such
      // equality as a definition creates false duplicates and disables the ordering edge.
      const definitions = envs.filter((e) => containsNotation(titleById.get(e.id) ?? "", symbol));
      if (definitions.length !== 1) continue;
      const def = definitions[0];
      for (const use of envs) {
        if (use.id === def.id || !containsNotation(`${titleById.get(use.id) ?? ""} ${use.body}`, symbol)) continue;
        if (!outgoing.get(def.id)!.has(use.id)) {
          outgoing.get(def.id)!.add(use.id);
          indegree.set(use.id, (indegree.get(use.id) ?? 0) + 1);
        }
      }
    }
    const ready = envs.filter((e) => indegree.get(e.id) === 0).map((e) => e.id);
    const out: P1Env[] = [];
    while (ready.length > 0) {
      ready.sort((a, b) => originalPos.get(a)! - originalPos.get(b)!);
      const id = ready.shift()!;
      out.push(byId.get(id)!);
      for (const to of outgoing.get(id) ?? []) {
        indegree.set(to, indegree.get(to)! - 1);
        if (indegree.get(to) === 0) ready.push(to);
      }
    }
    // Cycles or duplicate-definition ambiguities retain their stable input order; the semantic
    // reviewer still sees them and can request a wording repair rather than losing an environment.
    const emitted = new Set(out.map((e) => e.id));
    return [...out, ...envs.filter((e) => !emitted.has(e.id))];
  };
  // Locked envs: a P3-validated frozen body persisted on the node (`nl.frozen_body`) — used VERBATIM
  // so a P1 re-run cannot revert the tightening P3 reconciled to Lean. They are NOT rendered or
  // re-gated; they appear in the reviewed layer only so a loose env's `\ref` to a locked env resolves.
  // A delivery-role change invalidates the old P3 body. In particular, a theorem body frozen
  // before the node became `undelivered` must never be copied verbatim into a remark: that would
  // re-publish the very claim the delivery decision omitted. Undelivered nodes therefore always
  // take the loose path, where the deterministic renderer below replaces the body completely.
  // Citation-erased statements must be freshly rendered under the current policy. A body frozen
  // before this policy may expose the cited proposition as an ordinary paper assumption.
  const lockedNodes = nodes.filter((n) =>
    n.nl.frozen_body && n.delivery?.status !== "undelivered" && (citedDepsById.get(n.id)?.length ?? 0) === 0,
  );
  const looseNodes = nodes.filter((n) => !lockedNodes.includes(n));
  const lockedIds = new Set(lockedNodes.map((n) => n.id));
  for (const n of lockedNodes) if (n.nl.frozen_title != null) titleById.set(n.id, n.nl.frozen_title);
  const lockedEnvs: P1Env[] = lockedNodes.map((n) => ({
    id: n.id,
    env: envForNode(n)!,
    statement: n.nl.statement,
    body: normalizeCrefs(n.nl.frozen_body!),
    refSet: [...(refTargetsById.get(n.id) ?? [])],
  }));
  if (lockedNodes.length > 0) log(`locked (P3-validated frozen_body, verbatim — not re-rendered): ${[...lockedIds].join(", ")}`);

  // Lean-aware rendering: a theorem/lemma's PAPER statement is rendered DIRECTLY from its
  // machine-verified Lean signature (complete + curated), not from a possibly-loose NL "headline" —
  // so it carries every load-bearing hypothesis on the FIRST render and P3 confirms rather than
  // reconstructs (the headline gap is what made re-runs drift). Built for the loose theorem/lemma
  // nodes with a resolvable Lean decl; definitions/assumptions/statement-only keep the NL render.
  const kindById = new Map(nodes.map((n) => [n.id, n.kind] as const));
  const leanIndex = await buildLeanContextIndex(repoRoot, io.bank.leanSubdir);
  const leanCtxById = new Map<string, LeanContext>();
  for (const n of looseNodes) {
    if ((n.kind === "theorem" || n.kind === "lemma") && n.lean.decl_name && n.lean.file) {
      const ctx = await leanIndex.contextFor({ decl_name: n.lean.decl_name, file: n.lean.file });
      if (ctx) leanCtxById.set(n.id, ctx);
    }
  }
  if (leanCtxById.size > 0) log(`Lean-aware render: ${leanCtxById.size} theorem/lemma statement(s) will render from Lean`);

  const assemble = (envs: P1Env[]): string =>
    [
      "% Frozen formal layer — causalsmith P1 (graph render). Bodies are hash-pinned; do not edit.",
      ...orderByNotationDefinitions([...envs, ...lockedEnvs]).flatMap((e) => {
        const t = titleById.get(e.id);
        return [`\\begin{${e.env}}{${e.id}}${t ? `[${t}]` : ""}`, e.body, `\\end{${e.env}}`, ""];
      }),
    ].join("\n");

  // The semantic reviewer treats `D_{G_i t}` and `D_{G_i,t}` as distinct notation.
  // Synthesized prose used to oscillate between the two spellings across repair rounds,
  // consuming the bounded loop without changing any mathematical content. Keep the graph's
  // comma-free cohort-time convention for synthetic setup definitions only.
  const normalizeSynthNotation = (body: string): string =>
    body
      // Raw LaTeX such as `\\to` is a valid JSON `\\t` escape followed by
      // `o`; JSON.parse then produces a literal tab and invalid TeX.
      .replace(/\t(?=[A-Za-z])/g, "\\\\t")
      .replace(/D_\{G_i,\s*t\}/g, "D_{G_i t}");
  const recoveredSynthBodies = new Map<string, string>();

  /** Parse the delimiter-based render output (robust to multi-line LaTeX, which a
   *  JSON container mangles via unescaped newlines). Format per env:
   *    @@@ENV <obj_id>@@@\nTITLE: <title>\n@@@BODY@@@\n<body…>\n@@@END@@@        */
  const parseRender = (text: string): Map<string, { title?: string; body: string }> => {
    const out = new Map<string, { title?: string; body: string }>();
    const re = /@@@ENV\s+(\S+?)@@@\s*\n(?:TITLE:\s*(.*)\n)?@@@BODY@@@\s*\n([\s\S]*?)\n?@@@END@@@/g;
    let m: RegExpExecArray | null;
    while ((m = re.exec(text))) {
      const body = m[3].trim();
      if (body !== "") out.set(m[1].trim(), { title: m[2]?.trim() || undefined, body });
    }
    return out;
  };

  const BATCH = 6;
  type RenderReq = { id: string; statement: string; refSet: string[]; priorBody?: string; defects?: string[]; delivery?: P1Env["delivery"] };
  const enforceUndeliveredDisclosure = (r: RenderReq, body: string): string => {
    if (r.delivery?.status !== "undelivered") return body;
    const framed = undeliveredRemarkBody(r.statement, r.delivery.reason, body);
    if (framed !== body.trim()) titleById.set(r.id, "Open direction");
    return framed;
  };
  const renderBatch = async (reqs: RenderReq[]): Promise<Map<string, RenderHit>> => {
    const res = await deps.runCodex({
      prompt: await presentationPrompt("p1_touchup", {
        notation_table: notation,
        envs_block: reqs
          .map((r) =>
            [
              `### ${r.id}`,
              `ref_set: ${r.refSet.join(", ") || "(none)"}`,
              `cited_dependencies: ${citedPromptFor(r.id)}`,
              r.delivery ? `delivery_status: ${r.delivery.status}\ndelivery_role: ${r.delivery.role ?? "secondary"}\ndelivery_reason: ${r.delivery.reason}\nenvironment: remarkv` : "",
              `statement: ${r.statement}`,
              r.priorBody ? `prior_body: ${r.priorBody}` : "",
              r.defects ? `defects: ${r.defects.join(" | ")}` : "",
            ]
              .filter(Boolean)
              .join("\n"),
          )
          .join("\n\n"),
      }),
      cwd: repoRoot,
      reasoningEffort: "medium",
      leanLsp: false,
    });
    const parsed = parseRender(res.stdout);
    if (parsed.size < reqs.length) {
      await writeFile(join(io.outDir, "p1_render_raw.txt"), res.stdout.slice(0, 20000), "utf8");
    }
    return parsed;
  };

  // Cache key for a Lean-rendered env: depends on the LEAN statement (so an edited Lean re-renders),
  // not the NL headline. Separate from `renderKey` so the two render modes never collide.
  // `modelCacheKey` and `delivery` are included for the same reason `renderKey` includes
  // them: without them a model switch or a PRESENTATION_PROSE_POLICY_VERSION bump re-drafts
  // definitions/assumptions but silently reuses cached prose for exactly the theorems and
  // lemmas — the paper's headline statements — and an env that flips to `undelivered` can
  // hit an entry rendered under its old delivery role.
  const leanKey = (r: RenderReq, ctx: LeanContext): string =>
    hashEnvBody([
      modelCacheKey,
      ctx.statement,
      [...r.refSet].sort().join(","),
      citedPromptFor(r.id),
      r.priorBody ?? "",
      (r.defects ?? []).join("|"),
      JSON.stringify(r.delivery ?? null),
      "lean-citation-erasure-v1",
    ].join("§"));
  /** Render one theorem/lemma statement directly from its Lean signature + referenced defs. Output is
   *  the same `@@@ENV/TITLE/BODY` envelope the NL render uses, so `parseRender` handles both. */
  const renderFromLean = async (r: RenderReq, ctx: LeanContext): Promise<RenderHit | null> => {
    const res = await deps.runCodex({
      prompt: await presentationPrompt("p1_render_from_lean", {
        obj_id: r.id,
        kind: kindById.get(r.id) ?? "theorem",
        lean_statement: ctx.statement,
        referenced_defs: ctx.referencedDefs || "(none indexed — the statement references no local definitions)",
        nl_statement: r.statement,
        ref_set: r.refSet.join(", ") || "(none)",
        cited_dependencies: citedPromptFor(r.id),
        notation_table: notation,
        prior_and_defects: r.defects ? `prior_body: ${r.priorBody ?? ""}\ndefects: ${r.defects.join(" | ")}` : "(first render — none)",
      }),
      cwd: repoRoot,
      reasoningEffort: "medium",
      leanLsp: false,
    });
    const hit = parseRender(res.stdout).get(r.id);
    if (!hit) await writeFile(join(io.outDir, "p1_render_from_lean_raw.txt"), res.stdout.slice(0, 20000), "utf8");
    return hit ?? null;
  };

  const render: P1LoopHooks["render"] = async (reqs) => {
    const out = new Map<string, string>();
    const canonicalOut = (): Map<string, string> =>
      new Map([...out].map(([id, body]) => [id, normalizeCrefs(body)]));
    const keyById = new Map<string, string>();
    const leanMiss: { r: RenderReq; ctx: LeanContext }[] = [];
    const nlMiss: RenderReq[] = [];
    for (const r of reqs) {
      const recoveredBody = !r.defects ? recoveredSynthBodies.get(r.id) : undefined;
      if (recoveredBody != null) {
        out.set(r.id, recoveredBody);
        continue;
      }
      const ctx = leanCtxById.get(r.id);
      const k = ctx ? leanKey(r, ctx) : renderKey(r);
      keyById.set(r.id, k);
      // A defect-driven render is itself evidence that the prior body is unsuitable. Never let
      // that response become a fixed point by reusing its cache entry on the next repair round.
      const hit = r.defects ? undefined : cache.render[k];
      if (hit) {
        out.set(r.id, r.id.startsWith("synth_")
          ? normalizeSynthNotation(hit.body)
          : enforceUndeliveredDisclosure(r, hit.body));
        if (hit.title) titleById.set(r.id, hit.title);
      } else if (ctx) leanMiss.push({ r, ctx });
      else nlMiss.push(r);
    }
    const total = leanMiss.length + nlMiss.length;
    if (total === 0) {
      log(`render: all ${reqs.length} env(s) cached`);
      log(`render: ${out.size}/${reqs.length} bodies`);
      return canonicalOut();
    }
    log(`render: ${reqs.length - total} cached, ${leanMiss.length} from Lean + ${nlMiss.length} from NL via codex${reqs[0]?.defects ? " (re-render)" : ""}…`);
    // Lean-aware renders run per-node (bounded concurrency); a parse-miss falls back to the NL batch.
    const leanFallback: RenderReq[] = [];
    await mapLimit(leanMiss, 4, async ({ r, ctx }) => {
      const hit = await renderFromLean(r, ctx);
      if (hit) {
        out.set(r.id, enforceUndeliveredDisclosure(r, hit.body));
        if (hit.title) titleById.set(r.id, hit.title);
        cache.render[keyById.get(r.id)!] = hit;
      } else leanFallback.push(r);
    });
    const nlAll = [...nlMiss, ...leanFallback];
    if (nlAll.length > 0) {
      const chunks: RenderReq[][] = [];
      for (let i = 0; i < nlAll.length; i += BATCH) chunks.push(nlAll.slice(i, i + BATCH));
      const maps = await Promise.all(chunks.map((c) => renderBatch(c)));
      const missById = new Map(nlAll.map((r) => [r.id, r]));
      for (const m of maps) {
        for (const [id, hit] of m) {
          const req = missById.get(id);
          out.set(id, req?.id.startsWith("synth_")
            ? normalizeSynthNotation(hit.body)
            : req ? enforceUndeliveredDisclosure(req, hit.body) : hit.body);
          if (hit.title) titleById.set(id, hit.title);
          if (missById.has(id)) cache.render[keyById.get(id)!] = hit;
        }
      }
      // A long batched model response can occasionally omit one otherwise-valid envelope.
      // Recover only the missing members once, instead of discarding every successful body and
      // repaying for the whole batch. runP1Loop still fail-closes if the targeted retry misses.
      const missing = nlAll.filter((r) => !out.has(r.id));
      if (missing.length > 0) {
        log(`render: targeted retry for ${missing.length} omitted env(s) — ${missing.map((r) => r.id).join(", ")}`);
        const retries = await Promise.all(missing.map((r) => renderBatch([r])));
        for (let i = 0; i < missing.length; i++) {
          const r = missing[i];
          const hit = retries[i].get(r.id);
          if (!hit) continue;
          out.set(r.id, r.id.startsWith("synth_")
            ? normalizeSynthNotation(hit.body)
            : enforceUndeliveredDisclosure(r, hit.body));
          if (hit.title) titleById.set(r.id, hit.title);
          cache.render[keyById.get(r.id)!] = hit;
        }
      }
    }
    await saveCache();
    log(`render: ${out.size}/${reqs.length} bodies`);
    return canonicalOut();
  };

  const review: P1LoopHooks["review"] = async (layer, envs) => {
    log("review: lints + codex notation…");
    // `known` must include the LOCKED env ids too: they are present in the assembled layer (as fixed
    // context so loose-env xrefs resolve), so `lintAnchors` would otherwise flag each as
    // `unknown-objid` — a finding with no objId that the locked-filter below cannot drop.
    const known = new Set([...envs.map((e) => e.id), ...lockedIds]);
    const lintProblems: LintProblem[] = [
      ...lintAnchors(layer, known, null),
      ...lintClarity(layer),
      ...lintSelfContainment(layer),
      ...lintCrossRefs(layer, refTargetsById),
      ...lintReferences(layer),
      ...lintHypothesisPresentation(layer),
    ];
    const findings: P1Finding[] = lintProblems.map(toFinding);
    // Orphan classes → synthesize-def (clean symbol carried for the handler).
    for (const o of orphanParameterizedClasses(layer)) {
      findings.push({ gate: "notation-undefined", fixLocus: "synthesize-def", symbol: o.symbol, detail: `class ${o.symbol} used in ${o.usedIn.join("/")} with no defining env` }); // why: deterministic orphan findings must not be treated like advisory reviewer notation.
    }
    // Codex reviewer (medium effort on 5.5): semantic notation-resolvability
    // (catches \mathrm operators, wrong cross-refs, prose-only defs the deterministic backstop
    // misses). Cached by layer hash — an unchanged layer (e.g. a re-run) is not re-reviewed.
    const anchored = parseAnchoredEnvs(layer);
    const duplicateSynthFinding = (f: P1Finding): boolean =>
      f.fixLocus === "synthesize-def" && !!f.symbol && anchored.some((e) =>
        containsNotation(e.title ?? "", f.symbol!) || sameEstimatorNotationFamily(e.title ?? "", f.symbol!)
      );
    // Lean-realized symbols are filtered out of the ACTION list below
    // (`isLeanRealizedNotation`) because a paper-side duplicate would compete with the
    // Lean declaration for authority. That decision was invisible to the reviewer, which
    // therefore re-derived the same gaps every round — in one run `q_k`/`p_k`/`\pi_k`/
    // `\mu_{ak}` were re-reported 7/6/6/5 times across 10 high-effort ~39.5k-char calls,
    // all of them structurally unactionable. Tell the reviewer instead of discarding its
    // output. Part of the cache key: a changed realization set changes the valid findings.
    const realizedList = realizedSymbols.length > 0
      ? realizedSymbols.map((s) => `- ${s}`).join("\n")
      : "(none — this paper has no @realizes-tagged symbols)";
    const layerKey = hashEnvBody(`notation-definition-order-v9§${deps.codexModel ?? "?"}§${layer}§${notation}§${realizedList}`);
    if (cache.notation[layerKey]) {
      // Cached model findings are advisory evidence, not authority. Reapply
      // deterministic duplicate suppression on every read so an old spelling
      // mismatch cannot survive a parser improvement and burn the repair cap.
      findings.push(...cache.notation[layerKey].filter((f) => !duplicateSynthFinding(f)));
    } else {
      try {
        const res = await deps.runCodex({
          prompt: await presentationPrompt("p1_notation_check", {
            frozen_layer: layer,
            notation_table: notation,
            lean_realized_symbols: realizedList,
          }),
          cwd: repoRoot,
          reasoningEffort: "medium",
          leanLsp: false,
        });
        const problems = parseNotationReviewerOutput(res.stdout);
        const notationFindings: P1Finding[] = problems
          .filter((p) => p.symbol)
          .flatMap<P1Finding>((p): P1Finding[] => {
            const symbol = p.symbol!;
            const detail = `${p.symbol} [${p.case ?? "?"}] in ${(p.used_in ?? []).join("/")} — ${p.fix ?? ""}`;
            if (p.case === "undefined" || p.case === "no-anchor") {
              // Deterministic evidence wins over reviewer resampling: a titled anchored
              // definition means the symbol is not undefined. Synthesizing a duplicate here
              // creates mismatched notation and can induce dangling synthetic cross-references.
              if (anchored.some((e) =>
                containsNotation(e.title ?? "", symbol) || sameEstimatorNotationFamily(e.title ?? "", symbol)
              )) return [];
              return [{ gate: "notation-reviewer", symbol, fixLocus: "synthesize-def", detail }];
            }
            if (p.case === "wrong-ref" || p.case === "mismatch") {
              return (p.used_in ?? []).map((objId) => ({
                gate: "notation-reviewer",
                objId,
                fixLocus: "wording-revise" as const,
                detail,
              }));
            }
            return [{ gate: "notation-reviewer", symbol, fixLocus: "halt", detail }];
          });
        cache.notation[layerKey] = notationFindings;
        await saveCache();
        findings.push(...notationFindings);
      } catch (e) {
        io.state.notes.push(`P1 notation review skipped (deterministic floor still applied): ${(e as Error).message?.slice(0, 120)}`);
      }
    }
    // Locked envs are P3-validated and used verbatim — never surface a finding against them (they
    // are not in the loop's env set, so any lint hit on the context copy would just stall the loop).
    // Report what the reviewer emitted but the pipeline discarded. A silently dropped
    // finding is indistinguishable from a reviewer that never raised it, which is how the
    // Lean-realized re-report loop stayed invisible across runs.
    const leanSuppressed = findings.filter(
      (f) => f.fixLocus === "synthesize-def" && isLeanRealizedNotation(f.symbol),
    );
    if (leanSuppressed.length > 0) {
      log(
        `notation: suppressed ${leanSuppressed.length} synthesize-def finding(s) for Lean-realized ` +
          `symbol(s) ${leanSuppressed.map((f) => f.symbol).join(", ")} — the reviewer should have ` +
          `been told these are resolvable; recurrence across rounds means the prompt is not landing`,
      );
    }
    return findings.filter((f) =>
      (!f.objId || !lockedIds.has(f.objId)) &&
      !duplicateSynthFinding(f) &&
      // A paper-side definition is unnecessary when the notation already has an
      // explicit Lean realization. P2 links these symbols directly to `sym:*`;
      // synthesizing a second definition weakens the trust story and creates the
      // duplicate setup blocks seen in the panel-PPML presentation.
      !(f.fixLocus === "synthesize-def" && isLeanRealizedNotation(f.symbol))
    );
  };

  const synthResumeMarker = `% causalsmith-p1-synth model=${deps.codexModel ?? "?"} version=notation-definition-order-v7`;
  let synthCount = 0;
  const recoveredSynth: P1Env[] = [];
  const graphDefinitionNotation = nodes
    .filter((n) => n.kind === "setup" || n.kind === "definition" || n.kind === "assumption")
    .map((n) => `${n.nl.frozen_title ?? ""} ${n.nl.statement}`);
  // A capped semantic loop can spend many model calls building valid setup definitions before
  // discovering one deeper missing symbol. Persisted rejected output is therefore a resumable
  // receipt, not disposable scratch. Reuse only an explicitly model/version-stamped layer so a
  // model switch or prompt migration cannot silently carry old authored prose forward.
  const rejectedPath = join(io.outDir, "formal_layer_rejected.tex");
  const rejected = await readFile(rejectedPath, "utf8").catch(() => "");
  if (rejected.startsWith(synthResumeMarker)) {
    const recoveredCandidates = parseAnchoredEnvs(rejected)
      .filter((x) => /^synth_\d+$/.test(x.obj_id))
      .sort((a, b) => Number(a.obj_id.slice("synth_".length)) - Number(b.obj_id.slice("synth_".length)));
    const recoveredFamilies = new Set<string>();
    for (const e of recoveredCandidates) {
      const n = Number(e.obj_id.slice("synth_".length));
      if (Number.isFinite(n)) synthCount = Math.max(synthCount, n);
      // A title is the durable declaration of which notation a synthetic block
      // owns. Titleless rejected output cannot be safely deduplicated or placed;
      // let the live reviewer request it again instead of replaying ambiguity.
      if (!e.title) {
        io.state.notes.push(`P1: discarded titleless recovered notation definition ${e.obj_id}`);
        continue;
      }
      const mathFragments = [...e.title.matchAll(/\$([^$]+)\$|\\\((.*?)\\\)|\\\[([\s\S]*?)\\\]/g)]
        .map((m) => m[1] ?? m[2] ?? m[3]).filter((x): x is string => !!x);
      if (mathFragments.length === 0) {
        io.state.notes.push(`P1: discarded recovered notation definition ${e.obj_id} with no parseable notation in its title`);
        continue;
      }
      const hasLeanHome = mathFragments.some((fragment) => isLeanRealizedNotation(fragment));
      const familyPeer = [...recoveredFamilies, ...titleById.values()]
        .some((title) => sameEstimatorNotationFamily(title, e.title!)) ||
        graphDefinitionNotation.some((text) => sameEstimatorNotationFamily(text, e.title!));
      if (hasLeanHome || familyPeer) {
        io.state.notes.push(`P1: discarded duplicate recovered notation definition ${e.obj_id}`);
        continue;
      }
      recoveredFamilies.add(e.title);
      titleById.set(e.obj_id, e.title);
      const body = normalizeSynthNotation(e.body.trim());
      recoveredSynth.push({ id: e.obj_id, env: "definitionv", statement: body, body, refSet: [] });
      recoveredSynthBodies.set(e.obj_id, body);
    }
    if (recoveredSynth.length > 0) log(`resume: recovered ${recoveredSynth.length} model-matched synthesized definition(s)`);
  }
  const synthesize: P1LoopHooks["synthesize"] = async (symbols) => {
    const out: P1Env[] = [];
    // A notation-heavy setup can legitimately expose more than four missing
    // anchors at once (panel arrays + collapsed design + target definitions).
    // Keep synthesis bounded, but allow eight per round so the four-round loop
    // can repair up to 32 anchors instead of failing solely by batch arithmetic.
    for (const symbol of symbols.slice(0, 8)) {
      // Defensive backstop: even if a future reviewer bypasses the filtering
      // above, an `@realizes` symbol must never become presentation-synthesized.
      if (isLeanRealizedNotation(symbol)) continue;
      // A reviewer may spell an already-defined estimator with its semantic
      // tag in a different script position.  Do not create a second synthetic
      // definition for that cosmetic variant.
      if ([...titleById.values()].some((title) => sameEstimatorNotationFamily(title, symbol))) continue;
      try {
        const res = await deps.runCodex({
          prompt: await presentationPrompt("p1_synthesize_definition", {
            symbol,
            usages: "(used in the frozen layer; see the notation table)",
            note_md: io.bank.noteMd,
            lean_subdir: io.bank.leanSubdir,
          }),
          cwd: repoRoot,
          reasoningEffort: "medium",
          leanLsp: true,
        });
        const p = parseJsonLoose(res.stdout) as { title?: string; body?: string } | null;
        if (!p?.body || /\\(begin|end|label)\b/.test(p.body)) continue;
        const id = `synth_${++synthCount}`;
        if (p.title) titleById.set(id, p.title);
        const body = normalizeSynthNotation(p.body.trim());
        out.push({ id, env: "definitionv", statement: body, body, refSet: [] });
        io.state.notes.push(`P1: synthesized definition ${id} for orphan class ${symbol}`);
      } catch {
        /* best-effort: leave the orphan for the next review round / checkpoint */
      }
    }
    return out;
  };

  // ── Build the initial env set and run the loop (over the LOOSE nodes only; locked envs bypass it).
  // Higher synth ids were discovered as prerequisites in later review rounds, so place them
  // first when recovering an older append-ordered rejected layer.
  const envs0: P1Env[] = [...recoveredSynth.reverse(), ...looseNodes.map((n) => ({
    id: n.id,
    env: envForNode(n)!,
    statement: n.nl.statement,
    body: n.nl.statement,
    refSet: [...(refTargetsById.get(n.id) ?? [])],
    ...(n.delivery?.status === "undelivered"
      ? { delivery: { status: "undelivered" as const, role: n.delivery.role, reason: n.delivery.reason ?? "the item is outside the delivered theorem inventory" } }
      : {}),
  }))];
  const onRound: P1LoopHooks["onRound"] = async ({ phase, iter, envs, findings }) => {
    // Always persist the latest layer so a slow/timed-out run leaves the render on disk.
    await writeFile(join(io.outDir, "formal_layer.tex"), assemble(envs) + "\n", "utf8");
    if (phase === "render0") log(`render0: persisted ${envs.length}-env layer to formal_layer.tex`);
    else {
      const blocking = (findings ?? []).filter((f) => f.gate !== "xref-missing" && !(f.gate === "notation-undefined" && f.fixLocus == null));
      log(`review iter ${iter}: ${findings?.length ?? 0} finding(s) (${blocking.length} actionable) — ${[...new Set(blocking.map((f) => f.gate))].join(", ") || "clean"}`);
    }
  };
  const result = await runP1Loop(envs0, { render, review, synthesize, assemble, onRound, maxIterations: 6 });
  log(`loop: ${result.ok ? "converged" : "did NOT converge"} in ${result.iterations} iter(s); ${result.advisories.length} advisory`);

  const layer = assemble(result.envs);
  if (!result.ok) {
    await writeFile(join(io.outDir, "formal_layer_rejected.tex"), synthResumeMarker + "\n" + layer + "\n", "utf8");
    throw new Error(
      `P1 loop did not converge in ${result.iterations} iterations: ` +
        result.unresolved.map((f) => `[${f.gate}] ${f.objId ?? ""} ${f.detail}`).join("; "),
    );
  }
  // Source of truth: the formal layer as typed JSON blocks (obj_id = node id, lean/status/ref_set
  // from the graph), with a per-block body_hash freeze. The `.tex` is a DERIVED read-only view for
  // human review; the freeze lives in each block's body_hash (no standalone frozen_hashes.json).
  // See docs/superpowers/specs/2026-06-25-causalsmith-p1-json-formal-layer-design.md.
  // Frozen layer = loop-rendered bodies for loose nodes + verbatim frozen_body for locked nodes,
  // in topological `nodes` order (keeps the derived .tex view stable).
  const looseBody = new Map(result.envs.map((e) => [e.id, e.body]));
  const bodies = new Map(nodes.map((n) => [
    n.id,
    normalizeCrefs(presentedBody(n.delivery?.status, n.nl.frozen_body, looseBody.get(n.id))),
  ] as const));
  const graphIds = new Set(nodes.map((n) => n.id));
  const orderedResultEnvs = orderByNotationDefinitions(result.envs);
  const syntheticEnvs = orderedResultEnvs.filter((e) => !graphIds.has(e.id));
  const syntheticBlocks: FormalBlock[] = syntheticEnvs.map((e) => ({
    obj_id: e.id,
    alias: null,
    kind: "definition",
    env: "definitionv",
    title: titleById.get(e.id) ?? null,
    body: e.body,
    ref_set: [],
    lean: null,
    status: "presentation-synthesized",
    provenance: "presentation-synthesized",
    cited_dependencies: [],
    body_hash: hashBody(e.body),
  }));
  const graphBlocks = blocksFromGraph(
    graph,
    bodies,
    titleById,
    parseOutline(outlineMd).envOverrides,
    log,
    { citeKeyByNodeId: citeKeyById, locatorByNodeId: locatorById },
  );
  const blockById = new Map([...graphBlocks, ...syntheticBlocks].map((b) => [b.obj_id, b] as const));
  const finalOrder = parseAnchoredEnvs(assemble(result.envs)).map((e) => e.obj_id);
  const blocks = finalOrder.flatMap((id) => {
    const block = blockById.get(id);
    return block ? [block] : [];
  });
  const placedOutline = placeSynthesizedDefinitions(outlineMd, syntheticEnvs.map((e) => e.id));
  await writeFile(join(io.outDir, "outline.md"), placedOutline, "utf8");
  await writeFile(
    join(io.outDir, "formal_layer.json"),
    JSON.stringify(FormalLayerSource.parse({ commit: null, blocks }), null, 2) + "\n",
    "utf8",
  );
  await writeFile(
    join(io.outDir, "formal_layer.tex"),
    "% DERIVED from formal_layer.json — read-only, do not edit.\n" + blocksToTex(blocks) + "\n",
    "utf8",
  );

  // ── STATEMENT EQUIVALENCE AUDIT (co-located with statement production). Each frozen env body is
  // reconciled against its Lean declaration the moment it is rendered; drift is refined toward Lean
  // and the validated body is persisted onto the graph (nl.frozen_body) so a re-run stays tight. A
  // residual drift the auto-refiner could not close halts P1 for adjudication — the statement reaches
  // the outline checkpoint already verified against Lean, so P2/P3 confirm rather than reconstruct.
  log("statement audit: reconciling frozen envs against Lean…");
  const eqProblems = await runStatementAudit(io);
  if (eqProblems.length > 0) {
    io.state.hard_gate_failures = eqProblems;
    throw new Error(
      `P1 statement equivalence audit failed (${eqProblems.length} statement(s) still drift after up to 2 ` +
        `refinement rounds; the frozen layer disagrees with Lean beyond what auto-refinement could tighten — ` +
        `adjudicate or fix the graph statement): ` +
        eqProblems.map((p) => p.detail).join("; "),
    );
  }
  log("statement audit: all frozen envs faithful to Lean");

  // Advisory cross-reference findings → checkpoint note (never blocking).
  if (result.advisories.length > 0) {
    io.state.notes.push(
      `P1 cross-reference advisories (${result.advisories.length}, for checkpoint review): ` +
        result.advisories.map((f) => f.detail).join("; "),
    );
  }
  await writeFile(
    join(io.outDir, "notation_review.json"),
    JSON.stringify({ ok: result.ok, iterations: result.iterations, advisories: result.advisories }, null, 2) + "\n",
    "utf8",
  );
}
