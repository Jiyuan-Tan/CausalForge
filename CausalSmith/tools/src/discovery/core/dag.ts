// Build the formalization dependency graph straight from a typed `core`.
//
// The D0 core already encodes the graph implicitly: `statement.depends_on` is the
// proof DAG, `definition.by_member_properties` carves a class out of member-atoms,
// and `assumption.used_by` is the reverse edge. This module turns those fields into
// the explicit graph object the F-stages consume — so F1/F2 never re-extract
// structure from prose. See CausalSmith/doc/research/F1_F2_PLAN_REDESIGN.md §2.
import { coreNodeIds, type Core } from "./schema.js";

export type CoreNodeKind =
  | "assumption"
  | "definition-class"
  | "definition-construction"
  | "statement";

export interface CoreDag {
  /** All addressable core node ids (assumptions ∪ definitions ∪ statements). */
  nodes: Set<string>;
  /** node id → its kind. */
  kindOf: Map<string, CoreNodeKind>;
  /** class def id → its member-atom ids (from `by_member_properties`). */
  classMembers: Map<string, string[]>;
  /** member-atom id → the class def id that owns it (first owner, if several). */
  memberOwner: Map<string, string>;
  /** statement id → the assumption/definition ids it directly depends on. */
  assumptionDeps: Map<string, string[]>;
  /** statement id → the statement ids (lemmas) it directly depends on. */
  statementDeps: Map<string, string[]>;
}

/** Construct the explicit dependency graph from a typed core. Pure; no LLM. */
export function buildDagFromCore(core: Core): CoreDag {
  const nodes = coreNodeIds(core);

  const kindOf = new Map<string, CoreNodeKind>();
  for (const a of core.assumptions) kindOf.set(a.id, "assumption");
  for (const d of core.definitions) {
    kindOf.set(d.id, d.by_member_properties !== undefined ? "definition-class" : "definition-construction");
  }
  for (const s of core.statements) kindOf.set(s.id, "statement");

  const classMembers = new Map<string, string[]>();
  const memberOwner = new Map<string, string>();
  for (const d of core.definitions) {
    if (d.by_member_properties === undefined) continue;
    classMembers.set(d.id, d.by_member_properties);
    for (const m of d.by_member_properties) {
      if (!memberOwner.has(m)) memberOwner.set(m, d.id);
    }
  }

  const assumptionDeps = new Map<string, string[]>();
  const statementDeps = new Map<string, string[]>();
  for (const s of core.statements) {
    const assumptionLike: string[] = [];
    const statementLike: string[] = [];
    for (const dep of s.depends_on) {
      if (kindOf.get(dep) === "statement") statementLike.push(dep);
      else assumptionLike.push(dep); // assumption | definition (class/construction)
    }
    assumptionDeps.set(s.id, assumptionLike);
    statementDeps.set(s.id, statementLike);
  }

  return { nodes, kindOf, classMembers, memberOwner, assumptionDeps, statementDeps };
}
