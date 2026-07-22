// The F1 plan gate (CausalSmith/doc/research/F1_F2_PLAN_REDESIGN.md §7).
//
// Mechanical, no LLM. Runs on the plan right after F1 (self-check), as F1.5's
// pre-review lint, and after F2's sync-back. Enforces the one-to-one invariant —
// every core node maps to exactly one Lean object, no orphan Lean — plus kind/
// member/hyp consistency. A whole class of plan defects never reaches the
// reuse-soundness reviewer. The prose-faithfulness checks of the old F1.5
// (F/Q/N/L/P) are retired; H/U/X survive here as P2/P4/P7.
import type { Core } from "../../discovery/core/schema.js";
import { coreNodeIds } from "../../discovery/core/schema.js";
import { buildDagFromCore } from "../../discovery/core/dag.js";
import { PlanSchema, deriveFeasibility, type Plan } from "./schema.js";

export type PlanGateCode =
  | "schema"
  | "P1" // coverage
  | "P2" // member consistency
  | "P3" // kind consistency
  | "P4" // hyp closure
  | "P5" // reuse existence
  | "P6" // module resolution
  | "P7" // orphan Lean (emitted-tag correspondence)
  | "P8" // derived-feasibility consistency
  | "P9" // cited mapping (D0 status:"cited" ↔ gate_class:"cited"; source resolution)
  | "P10"; // undelivered guard (secondary theorem or cited node only; never load-bearing)

export interface PlanGateViolation {
  code: PlanGateCode;
  where: string;
  message: string;
}

export interface PlanGateResult {
  ok: boolean;
  violations: PlanGateViolation[];
}

export interface PlanGateOptions {
  /** Library-index decl names; when present, enables P5 (reuse existence). */
  knownDecls?: Set<string>;
  /** Importable module paths; when present, P6 requires membership (else format-only). */
  knownModules?: Set<string>;
  /** Tags parsed from emitted Lean (`-- @node` / `-- @env`); enables P7. F2 only. */
  leanTags?: { nodes: Set<string>; envs: Set<string> };
  /** All emitted Lean declaration names. Catches stale untagged declarations for an
   * undelivered plan node, which tag-only P7 cannot see. */
  leanDeclNames?: Set<string>;
}

const MODULE_RE = /^[A-Z][A-Za-z0-9_]*(\.[A-Za-z0-9_]+)*$/;

export function runPlanGate(planInput: unknown, core: Core, opts: PlanGateOptions = {}): PlanGateResult {
  const violations: PlanGateViolation[] = [];

  const parsed = PlanSchema.safeParse(planInput);
  if (!parsed.success) {
    for (const issue of parsed.error.issues) {
      violations.push({ code: "schema", where: issue.path.join(".") || "<root>", message: issue.message });
    }
    return { ok: false, violations };
  }
  const plan: Plan = parsed.data;
  const dag = buildDagFromCore(core);
  const nodeIds = coreNodeIds(core);
  const symbolNames = new Set(core.symbols.map((s) => s.name));
  const classIds = new Set([...dag.kindOf].filter(([, k]) => k === "definition-class").map(([id]) => id));
  const assumptionIds = new Set([...dag.kindOf].filter(([, k]) => k === "assumption").map(([id]) => id));
  const gateIds = new Set(Object.entries(plan.nodes).filter(([, n]) => n.gate).map(([id]) => id));
  // DISCHARGED assumptions: a core `assumption` node the plan reclassifies to a proved
  // `lemma`/`theorem` (the substrate-fact discharge, route (2)→(1) / substrate-built
  // channel). It is no longer a hypothesis but a PROVED dependency the consumer's proof
  // uses, so P3 must allow the lemma/theorem kind and P4 must not demand it as a hyp.
  // (Semantic soundness — that the lemma is genuinely proved/reused, not a laundered
  // modeling assumption — is enforced downstream by F1.5 type-fit, F3 proof, and F4.)
  const dischargedAssumptions = new Set(
    [...assumptionIds].filter((id) => {
      const node = plan.nodes[id];
      if (!node) return false;
      // A proved lemma/theorem is the canonical discharged form; `disposition:"reuse"`
      // on an assumption is the same signal (it points at a real decl that proves the
      // fact — a modeling assumption is never "reused" from a library decl).
      return node.lean_kind === "lemma" || node.lean_kind === "theorem" || node.disposition === "reuse";
    }),
  );

  // P1: coverage. nodes keys == core node ids; symbols all bound by some S-block.
  const planNodeKeys = new Set(Object.keys(plan.nodes));
  for (const id of nodeIds) {
    if (!planNodeKeys.has(id)) violations.push({ code: "P1", where: id, message: `core node has no plan entry` });
  }
  for (const id of planNodeKeys) {
    if (!nodeIds.has(id)) violations.push({ code: "P1", where: id, message: `plan node is not a core node id` });
  }
  const boundSymbols = new Set<string>();
  for (const e of plan.env) {
    for (const s of e.binds_symbols) {
      boundSymbols.add(s);
      if (!symbolNames.has(s)) violations.push({ code: "P1", where: e.id, message: `binds unknown symbol '${s}'` });
    }
  }
  for (const s of symbolNames) {
    if (!boundSymbols.has(s)) violations.push({ code: "P1", where: `symbol:${s}`, message: `symbol bound by no S-block` });
  }

  // P3: kind consistency (per node id whose plan entry exists).
  for (const [id, node] of Object.entries(plan.nodes)) {
    const kind = dag.kindOf.get(id);
    if (kind === undefined) continue; // already flagged by P1
    const coreStmt = kind === "statement" ? core.statements.find((s) => s.id === id) : undefined;
    const want =
      // A core assumption is normally `assumption`, but may be DISCHARGED to a proved
      // `lemma`/`theorem` (substrate-fact discharge) — allow all three for assumptions.
      kind === "assumption" ? ["assumption", "lemma", "theorem"]
      : kind === "definition-class" ? ["structure"]
      : kind === "definition-construction" ? ["def"]
      : coreStmt && node.gate ? ["assumption"]
      : coreStmt?.kind === "openendedquestion" ? ["def"] // solved OEQs are replaced by thm: nodes at D0; only unresolved OEQs can reach F1.
      : ["theorem", "lemma"]; // statement
    if (!want.includes(node.lean_kind)) {
      violations.push({ code: "P3", where: id, message: `lean_kind '${node.lean_kind}' invalid for core ${kind} (expected ${want.join("|")})` });
    }
  }

  // P2: member consistency. A class node's `members` must equal the core's
  // by_member_properties for that class; every member is an assumption id.
  for (const classId of classIds) {
    const node = plan.nodes[classId];
    if (!node) continue;
    const coreMembers = new Set(dag.classMembers.get(classId) ?? []);
    const planMembers = new Set(node.members ?? []);
    for (const m of coreMembers) {
      if (!planMembers.has(m)) violations.push({ code: "P2", where: classId, message: `plan omits core member '${m}'` });
    }
    for (const m of planMembers) {
      if (!coreMembers.has(m)) violations.push({ code: "P2", where: classId, message: `plan lists non-member '${m}'` });
      else if (!assumptionIds.has(m)) violations.push({ code: "P2", where: classId, message: `member '${m}' is not an assumption` });
    }
  }

  // P4: hyp closure. hyps ⊆ depends_on; each hyp is an assumption or a class; every
  // assumption/def dependency is covered (directly, or via a class in hyps).
  for (const s of core.statements) {
    const node = plan.nodes[s.id];
    if (!node || (node.lean_kind !== "theorem" && node.lean_kind !== "lemma")) continue;
    const hyps = new Set(node.hyps ?? []);
    const depSet = new Set(s.depends_on);
    for (const h of hyps) {
      if (!depSet.has(h)) violations.push({ code: "P4", where: s.id, message: `hyp '${h}' is not in depends_on` });
      else if (!assumptionIds.has(h) && !classIds.has(h) && !gateIds.has(h)) {
        violations.push({ code: "P4", where: s.id, message: `hyp '${h}' is neither an assumption nor a class (cannot be a hypothesis)` });
      }
    }
    for (const dep of dag.assumptionDeps.get(s.id) ?? []) {
      if (!assumptionIds.has(dep)) continue; // only assumptions must surface as hyps; defs are used, not assumed
      if (dischargedAssumptions.has(dep)) continue; // discharged → a proved lemma the proof USES, not a hyp
      if (hyps.has(dep)) continue;
      const viaClass = [...classIds].some((c) => hyps.has(c) && (dag.classMembers.get(c) ?? []).includes(dep));
      if (!viaClass) violations.push({ code: "P4", where: s.id, message: `assumption dep '${dep}' is neither a hyp nor a member of a bundled class` });
    }
  }

  // P5: reuse existence (optional — needs the library index).
  if (opts.knownDecls) {
    const checkReuse = (where: string, decl: string | null | undefined) => {
      if (decl && !opts.knownDecls!.has(decl)) violations.push({ code: "P5", where, message: `reuse decl '${decl}' not found in library index` });
    };
    for (const e of plan.env) checkReuse(e.id, e.disposition === "reuse" ? e.reuse : null);
    for (const [id, n] of Object.entries(plan.nodes)) checkReuse(id, n.disposition === "reuse" ? n.reuse : null);
  }

  // P6: module resolution. Format always; membership when knownModules supplied.
  const checkModules = (where: string, mods: string[]) => {
    for (const m of mods) {
      if (!MODULE_RE.test(m)) violations.push({ code: "P6", where, message: `module '${m}' is not a valid module path` });
      else if (opts.knownModules && !opts.knownModules.has(m)) violations.push({ code: "P6", where, message: `module '${m}' does not resolve` });
    }
  };
  for (const e of plan.env) checkModules(e.id, e.modules);
  for (const [id, n] of Object.entries(plan.nodes)) checkModules(id, n.modules);

  // P7: orphan Lean — emitted tags correspond exactly to plan keys (F2 only).
  if (opts.leanTags) {
    const envIds = new Set(plan.env.map((e) => e.id));
    for (const t of opts.leanTags.nodes) {
      if (!planNodeKeys.has(t)) violations.push({ code: "P7", where: t, message: `emitted Lean tags '@node ${t}' but no plan entry` });
    }
    for (const id of planNodeKeys) {
      const undelivered = plan.nodes[id]?.delivery_status === "undelivered";
      if (undelivered && opts.leanTags.nodes.has(id)) {
        violations.push({ code: "P7", where: id, message: `undelivered node must not emit an '@node' Lean declaration` });
      } else if (!undelivered && !opts.leanTags.nodes.has(id)) {
        violations.push({ code: "P7", where: id, message: `delivered plan node has no emitted '@node' tag` });
      }
    }
    if (opts.leanDeclNames) {
      const names = new Set<string>();
      for (const name of opts.leanDeclNames) {
        names.add(name);
        names.add(name.split(".").at(-1) ?? name);
      }
      for (const id of planNodeKeys) {
        const node = plan.nodes[id];
        if (node.delivery_status !== "undelivered") continue;
        const shortName = node.lean_name.split(".").at(-1) ?? node.lean_name;
        if (names.has(node.lean_name) || names.has(shortName)) {
          violations.push({ code: "P7", where: id, message: `undelivered node still has Lean declaration '${node.lean_name}' (tagged or untagged)` });
        }
      }
    }
    for (const t of opts.leanTags.envs) {
      if (!envIds.has(t)) violations.push({ code: "P7", where: t, message: `emitted Lean tags '@env ${t}' but no S-block` });
    }
    for (const id of envIds) {
      if (!opts.leanTags.envs.has(id)) violations.push({ code: "P7", where: id, message: `planned S-block has no emitted '@env' tag` });
    }
  }

  // P8: stored feasibility must match the derived value.
  if (plan.feasibility && plan.feasibility !== deriveFeasibility(plan)) {
    violations.push({ code: "P8", where: "<root>", message: `feasibility '${plan.feasibility}' disagrees with derived '${deriveFeasibility(plan)}'` });
  }

  // P9: cited mapping. A D0 `status:"cited"` statement is BORROWED (D0 chose not to prove
  // it); F1 must PROPAGATE it as a `gate_class:"cited"` node — never silently re-launder it
  // into a crux/build lemma — and must not INVENT a citation for a non-cited statement.
  // Every node `source` must resolve to a declared `citations[]` entry.
  const citationIds = new Set(plan.citations.map((c) => c.id));
  for (const s of core.statements) {
    const node = plan.nodes[s.id];
    if (!node) continue; // P1 already flagged
    if (s.status === "cited") {
      if (!node.gate || node.gate_class !== "cited") {
        violations.push({ code: "P9", where: s.id, message: `core status:"cited" must map to a gate_class:"cited" plan node (got gate=${!!node.gate}, gate_class=${node.gate_class ?? "none"}) — re-laundering a citation` });
      }
      if (!node.source) {
        violations.push({ code: "P9", where: s.id, message: `cited node must set 'source' to a cite: id` });
      }
    } else if (node.gate_class === "cited") {
      violations.push({ code: "P9", where: s.id, message: `plan marks gate_class:"cited" but core status is '${s.status}' — F1 must not invent a citation` });
    }
  }
  for (const [id, n] of Object.entries(plan.nodes)) {
    if (n.source && !citationIds.has(n.source)) {
      violations.push({ code: "P9", where: id, message: `node 'source' '${n.source}' does not resolve to a citations[] entry` });
    }
  }

  // P10: `undelivered` is a narrow, disclosed presentation status — never a way
  // to hide a headline or a proof dependency. It is legal only for (a) a theorem
  // explicitly classified secondary, or (b) a cited node. It must be a leaf with
  // respect to every delivered statement, because a delivered result cannot rely
  // on an object that has no Lean declaration.
  const undeliveredIds = new Set(
    Object.entries(plan.nodes)
      .filter(([, n]) => n.delivery_status === "undelivered")
      .map(([id]) => id),
  );
  for (const id of undeliveredIds) {
    const node = plan.nodes[id];
    const stmt = core.statements.find((s) => s.id === id);
    const cited = !!stmt && stmt.status === "cited" && node.gate && node.gate_class === "cited";
    const secondaryTheorem =
      stmt?.kind === "theorem" && node.lean_kind === "theorem" && node.delivery_role === "secondary";
    if (!cited && !secondaryTheorem) {
      violations.push({
        code: "P10",
        where: id,
        message:
          `undelivered is legal only for a secondary theorem or a cited node ` +
          `(got kind=${stmt?.kind ?? "non-statement"}, role=${node.delivery_role ?? "none"}, cited=${cited})`,
      });
    }
    if (!node.delivery_reason) {
      violations.push({ code: "P10", where: id, message: `undelivered node must disclose a nonempty delivery_reason` });
    }
  }
  const statementById = new Map(core.statements.map((s) => [s.id, s] as const));
  for (const s of core.statements) {
    if (undeliveredIds.has(s.id)) continue;
    const seen = new Set<string>();
    const stack = [...s.depends_on];
    while (stack.length > 0) {
      const dep = stack.pop()!;
      if (seen.has(dep)) continue;
      seen.add(dep);
      if (undeliveredIds.has(dep)) {
        violations.push({
          code: "P10",
          where: s.id,
          message: `delivered statement transitively depends on undelivered node '${dep}'`,
        });
        break;
      }
      stack.push(...(statementById.get(dep)?.depends_on ?? []));
    }
  }

  return { ok: violations.length === 0, violations };
}
