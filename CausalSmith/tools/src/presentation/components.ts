// Composite-object component mapping: one paper definition/assumption is often
// formalized by SEVERAL Lean pieces (multiple decls, and/or named hypothesis
// binders of a theorem). This module owns the discovery (codex), the source
// assembly, and the content-keyed cache — shared by the P1 statement equivalence audit
// (verify the statement against ALL its pieces, not a single first-wins anchor)
// and the P4 emit (render the pieces as a composite). The single `lean` anchor
// in the crosswalk stays the "primary representative decl"; this is the full set.

import { readFile, readdir, realpath } from "node:fs/promises";
import { isAbsolute, join, relative, sep } from "node:path";
import { z } from "zod";
import { hashEnvBody, type AnchoredEnv } from "./tex_anchors.js";
import { loadJsonCache } from "./cache.js";
import { extractHypothesisBinders } from "./lean_extract.js";
import { parseJsonLoose } from "./gates.js";
import { presentationPrompt } from "./prompt_io.js";
import { writeJsonAtomic } from "./json_io.js";
import { graphComponentSpecs } from "./graph_components.js";
import { fullyQualifiedSourceDecls, resolveLeanDeclaration, type ResolvedLeanDeclaration } from "./declaration_resolver.js";
import type { CrosswalkEntry } from "./types.js";
import type { FormalizationGraph } from "../graph/types.js";

/** One mapped Lean piece of a composite (multi-decl / hypothesis-only) paper object. */
export type ComponentSpec =
  | { type: "decl"; decl: string }
  | { type: "hypotheses"; theorem: string; binders: string[] };

const ComponentSpecSchema = z.union([
  z.object({ type: z.literal("decl"), decl: z.string().min(1) }),
  z.object({ type: z.literal("hypotheses"), theorem: z.string().min(1), binders: z.array(z.string().min(1)) }),
]);
const ComponentsResponseSchema = z.object({ components: z.array(ComponentSpecSchema) });
const COMPONENT_DISCOVERY_POLICY = "component-discovery-v2";
const CachedComponentEntrySchema = z.object({
  policy: z.literal(COMPONENT_DISCOVERY_POLICY),
  key: z.string().min(1),
  complete: z.literal(true),
  components: z.array(ComponentSpecSchema),
});

export interface ModuleDecl {
  file: string;
  line: number;
  kind: string;
  decl?: string;
  sourceHash?: string;
}

/** codex runner shape (subset of PaperDeps.runCodex); kept local to avoid a
 *  runtime import cycle with pipeline.ts. */
export interface CodexRunner {
  runCodex: (a: {
    prompt: string;
    cwd: string;
    reasoningEffort?: "minimal" | "low" | "medium" | "high" | "xhigh";
    leanLsp?: boolean;
    /** Codex native sub-agents — default-off (opt-in); set true only for a lone low-concurrency call whose prompt uses spawn_agent (see CodexRunInput.multiAgent). */
    multiAgent?: boolean;
  }) => Promise<{ stdout: string; stderr: string }>;
}

/** Scan every `.lean` under the paper's module dir → short-name → location/kind
 *  (first definition wins). The candidate pool for resolving component pieces
 *  that are not standalone crosswalk entries. */
export async function buildModuleDeclIndex(
  repoRoot: string,
  leanSubdir: string,
): Promise<Map<string, ModuleDecl>> {
  const out = new Map<string, ModuleDecl>();
  const shortCandidates = new Map<string, ModuleDecl[]>();
  const ambiguousFull = new Set<string>();
  const root = join(repoRoot, leanSubdir);
  try {
    const rootReal = await realpath(root);
    const files = (await readdir(rootReal, { recursive: true })).map(String).filter((f) => f.endsWith(".lean"));
    for (const rel of files) {
      const fileReal = await realpath(join(rootReal, rel));
      const fromRoot = relative(rootReal, fileReal);
      if (fromRoot === ".." || fromRoot.startsWith(`..${sep}`) || isAbsolute(fromRoot)) {
        throw new Error(`P1 module declaration candidate symlink escapes run root: ${rel}`);
      }
      const source = await readFile(fileReal, "utf8");
      const sourceHash = hashEnvBody(source);
      for (const d of fullyQualifiedSourceDecls(source)) {
        if (out.has(d.name)) { out.delete(d.name); ambiguousFull.add(d.name); }
        else if (!ambiguousFull.has(d.name)) out.set(d.name, { file: rel, line: d.line, kind: d.kind, decl: d.name, sourceHash });
        const short = d.name.slice(d.name.lastIndexOf(".") + 1);
        const candidates = shortCandidates.get(short) ?? [];
        candidates.push({ file: rel, line: d.line, kind: d.kind, decl: d.name, sourceHash });
        shortCandidates.set(short, candidates);
      }
    }
  } catch (e) {
    if ((e as NodeJS.ErrnoException).code !== "ENOENT") throw e;
    /* absent run directory: fall back to crosswalk-only resolution */
  }
  for (const [short, candidates] of shortCandidates) {
    if (candidates.length === 1 && !out.has(short)) out.set(short, candidates[0]);
  }
  return out;
}

/** Decl pool string for the discovery prompt: crosswalk-backed decls + every
 *  def/abbrev/structure in the module index. */
export function buildDeclList(crosswalk: CrosswalkEntry[], moduleDecls: Map<string, ModuleDecl>): string {
  const defKinds = new Set(["def", "abbrev", "structure"]);
  return [
    ...new Set([
      ...crosswalk.filter((c) => c.lean).map((c) => `${c.lean!.decl} : ${c.lean!.file}`),
      ...[...moduleDecls.entries()].filter(([, v]) => defKinds.has(v.kind)).map(([n, v]) => `${n} : ${v.file}`),
    ]),
  ].join("\n");
}

/** The T-block statements, concatenated — the hypothesis ledgers the discovery
 *  (and the equivalence audit) reference for hypothesis-only assumptions. */
export async function buildTheoremStatements(
  crosswalk: CrosswalkEntry[],
  repoRoot: string,
  leanSubdir: string,
): Promise<string> {
  const parts: string[] = [];
  // Theorems by kind (node-id keyed crosswalk: ids are `t1`, not `T-1`).
  for (const t of crosswalk.filter((c) => c.kind === "theorem" && c.lean)) {
    const hit = await resolveLeanDeclaration(repoRoot, leanSubdir, t.lean!);
    parts.push(hit.snippet);
  }
  return parts.join("\n\n");
}

/** Resolve a component decl name to its source location: crosswalk first, then
 *  the module index. */
function resolveDecl(
  decl: string,
  crosswalk: CrosswalkEntry[],
  moduleDecls: Map<string, ModuleDecl>,
): { file: string; decl: string; line: number } | null {
  const c = crosswalk.find((x) => x.lean?.decl === decl);
  if (c?.lean) return { file: c.lean.file, decl: c.lean.decl, line: c.lean.line };
  const m = moduleDecls.get(decl);
  return m ? { file: m.file, decl: m.decl ?? decl, line: m.line } : null;
}

/** Codex discovery: which Lean pieces formalize this env body. Valid `[]` means
 *  genuinely unformalized; malformed output throws and is not cached. */
export async function discoverComponents(args: {
  envBody: string;
  declList: string;
  theoremStatements: string;
  deps: CodexRunner;
  repoRoot: string;
}): Promise<ComponentSpec[]> {
  const res = await args.deps.runCodex({
    prompt: await presentationPrompt("p4_components", {
      env_body: args.envBody,
      decl_list: args.declList,
      theorem_statements: args.theoremStatements,
    }),
    cwd: args.repoRoot,
    reasoningEffort: "medium",
    leanLsp: false,
  });
  const parsed = ComponentsResponseSchema.safeParse(parseJsonLoose(res.stdout));
  if (!parsed.success) {
    throw new Error(`component discovery returned invalid JSON: ${parsed.error.message}`); // why: malformed discovery must not cache as "no components".
  }
  return parsed.data.components;
}

/** Assemble a component set into readable Lean text (one labelled block per
 *  piece) for feeding an equivalence audit or the touch-up. Pieces that do not
 *  resolve are skipped. Empty string when nothing resolves. */
export async function assembleComponentText(args: {
  specs: ComponentSpec[];
  crosswalk: CrosswalkEntry[];
  moduleDecls: Map<string, ModuleDecl>;
  repoRoot: string;
  leanSubdir: string;
}): Promise<{ text: string; resolved: ResolvedLeanDeclaration[] }> {
  const blocks: string[] = [];
  const resolved: ResolvedLeanDeclaration[] = [];
  for (const spec of args.specs) {
    const named = spec.type === "decl" ? spec.decl : spec.theorem;
    const loc = resolveDecl(named, args.crosswalk, args.moduleDecls);
    if (!loc) throw new Error(`P1 component ${named} is not present in the crosswalk or run declaration index`);
    const hit = await resolveLeanDeclaration(args.repoRoot, args.leanSubdir, loc);
    resolved.push(hit);
    if (spec.type === "decl") blocks.push(`-- ${hit.decl}  (${hit.file})\n${hit.snippet}`);
    else {
      const hypotheses = extractHypothesisBinders(hit.snippet, spec.binders);
      const missing = spec.binders.filter((name) =>
        hypotheses.includes(`-- (binder ${name} not found in the statement)`));
      if (missing.length > 0) {
        throw new Error(`P1 component hypotheses {${missing.join(", ")}} are absent from ${hit.decl}`);
      }
      if (!hypotheses.trim()) throw new Error(`P1 component hypotheses {${spec.binders.join(", ")}} are absent from ${hit.decl}`);
      blocks.push(`-- hypotheses of ${hit.decl}  (${hit.file})\n${hypotheses}`);
    }
  }
  if (resolved.length !== args.specs.length) throw new Error("P1 component resolution was partial");
  return { text: blocks.join("\n\n"), resolved };
}

/** Stable signature of a component set (for cache keys / drift detection). */
export function componentSignature(specs: ComponentSpec[]): string {
  return specs
    .map((s) => (s.type === "decl" ? `d:${s.decl}` : `h:${s.theorem}:${[...s.binders].sort().join(",")}`))
    .sort()
    .join("|");
}

/**
 * Cache-backed component discovery for a set of envs. Idempotent: keyed on the
 * env body hash (stable across P3/P4 — both see the FROZEN paper bodies), so the
 * first stage to call computes and later stages reuse. Default selection mirrors
 * the original P4 rule: every definition/assumption env, plus any env with no
 * single standalone decl. Returns the obj_id → ComponentSpec[] map and the
 * module index (the caller needs it to assemble / render).
 */
export async function ensureComponentsForEnvs(args: {
  envs: AnchoredEnv[];
  crosswalk: CrosswalkEntry[];
  repoRoot: string;
  leanSubdir: string;
  cachePath: string;
  deps: CodexRunner;
  /** obj_id → the canonical formal content to discover/key on. Pass the F1 NOTE
   *  BLOCK body so the mapping is STABLE across P1 (mechanical bodies), P3, and P4
   *  (touched-up bodies) — the components depend on the math, not the prose, so
   *  one discovery is shared by all three. Falls back to the env body per obj_id. */
  noteBlocks?: Map<string, string>;
  select?: (e: AnchoredEnv, cw: CrosswalkEntry) => boolean;
  /** The formalization graph. When given, the component set of each selected env is read from
   *  the graph (own decl + statement-uses neighbours) FIRST; codex discovery is the fallback
   *  used only where the graph yields nothing — so no Lean piece is ever silently dropped. */
  graph?: FormalizationGraph;
}): Promise<{
  components: Record<string, ComponentSpec[]>;
  complete: Record<string, true>;
  moduleDecls: Map<string, ModuleDecl>;
}> {
  const cwById = new Map(args.crosswalk.map((c) => [c.obj_id, c]));
  // repair:false — values are Lean-derived text (not model-authored LaTeX) and zod-guarded below.
  const cache = await loadJsonCache<Record<string, unknown>>(args.cachePath, { repair: false });
  const moduleDecls = await buildModuleDeclIndex(args.repoRoot, args.leanSubdir);
  const declList = buildDeclList(args.crosswalk, moduleDecls);
  const select =
    args.select ??
    ((e: AnchoredEnv, cw: CrosswalkEntry) => {
      const isDefLike = e.env === "definitionv" || e.env === "algorithmv" || e.env === "assumptionv";
      return !(cw.lean && !isDefLike); // def/assumption envs + any env with no single decl
    });
  const contentFor = (e: AnchoredEnv) => args.noteBlocks?.get(e.obj_id) ?? e.body;
  // These inputs jointly define the discovery universe. A body-only key allowed
  // an old []/partial answer to survive changed declarations, statements, graph,
  // or crosswalk provenance and silently turn a formal object into note-only text.
  const theoremStatements = await buildTheoremStatements(args.crosswalk, args.repoRoot, args.leanSubdir);
  const canonicalCrosswalkSources: string[] = [];
  for (const cw of args.crosswalk) {
    if (!cw.lean) continue;
    const hit = await resolveLeanDeclaration(args.repoRoot, args.leanSubdir, cw.lean);
    canonicalCrosswalkSources.push(
      `${cw.obj_id}|${hit.file}|${hit.decl}|${hit.line}|${hashEnvBody(hit.snippet)}`,
    );
  }
  const candidateInventory = [...moduleDecls.entries()]
    .map(([name, d]) => `${name}|${d.decl ?? ""}|${d.file}|${d.line}|${d.kind}|${d.sourceHash ?? ""}`)
    .sort().join("\n");
  const provenance = JSON.stringify({
    crosswalk: args.crosswalk.map((c) => ({ obj_id: c.obj_id, kind: c.kind, verdict: c.verdict, lean: c.lean })),
    graph: args.graph ? {
      nodes: args.graph.nodes.map((n) => ({ id: n.id, obj_id: n.obj_id, provenance: n.provenance, lean: n.lean, review: n.review })),
      edges: args.graph.edges,
    } : null,
  });
  const discoveryUniverse = hashEnvBody(
    `${COMPONENT_DISCOVERY_POLICY}\n${declList}\n${candidateInventory}\n${canonicalCrosswalkSources.sort().join("\n")}\n${theoremStatements}\n${provenance}`,
  );
  const out: Record<string, ComponentSpec[]> = {};
  const complete: Record<string, true> = {};
  for (const e of args.envs) {
    const cw = cwById.get(e.obj_id);
    if (!cw || !select(e, cw)) continue;
    const content = contentFor(e);
    const key = hashEnvBody(`${COMPONENT_DISCOVERY_POLICY}|${discoveryUniverse}|${content}`);
    // Graph-first: the verified graph enumerates the Lean pieces deterministically. When it
    // yields a set, use it and skip codex discovery entirely (authoritative — overrides any
    // stale codex-discovered cache entry for the same content).
    const graphSpecs = args.graph ? graphComponentSpecs(args.graph, e.obj_id) : [];
    if (graphSpecs.length > 0) {
      out[e.obj_id] = graphSpecs;
      complete[e.obj_id] = true;
      cache[e.obj_id] = { policy: COMPONENT_DISCOVERY_POLICY, key, complete: true, components: graphSpecs };
      continue;
    }
    const parsedCache = CachedComponentEntrySchema.safeParse(cache[e.obj_id]);
    if (parsedCache.success && parsedCache.data.key === key) {
        out[e.obj_id] = parsedCache.data.components;
        complete[e.obj_id] = true;
        continue;
    }
    delete cache[e.obj_id]; // stale, incomplete, pre-policy, or malformed entries are never receipts.
    const comps = await discoverComponents({
      envBody: content,
      declList,
      theoremStatements,
      deps: args.deps,
      repoRoot: args.repoRoot,
    });
    out[e.obj_id] = comps;
    complete[e.obj_id] = true;
    cache[e.obj_id] = { policy: COMPONENT_DISCOVERY_POLICY, key, complete: true, components: comps };
  }
  await writeJsonAtomic(args.cachePath, cache);
  return { components: out, complete, moduleDecls };
}
