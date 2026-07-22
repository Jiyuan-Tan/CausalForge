import type { Core } from "./schema.js";
import { extractNodeRefs } from "./node_ids.js";

export interface AuthoredNodeReference {
  location: string;
  text: string;
}

/** Find literal node ids in authored mathematical/narrative text, not structured edges.
 *
 * A supersession may safely remap `depends_on`, but changing "the conditions in lem:x"
 * to name a different lemma is a claim edit. Keeping this inventory separate from the
 * graph is what prevents an edge migration from laundering that prose change. */
export function findAuthoredNodeReferences(
  core: Core,
  targetId: string,
  opts: { excludeNodeId?: string } = {},
): AuthoredNodeReference[] {
  const target = targetId.toLowerCase();
  const out: AuthoredNodeReference[] = [];
  const add = (location: string, text: string | undefined): void => {
    if (!text || !extractNodeRefs(text).includes(target)) return;
    out.push({ location, text });
  };

  add("target_estimand", core.target_estimand);
  add("estimand_functional", core.estimand_functional);
  add("tldr", core.tldr);
  add("related_work", core.related_work);
  add("interpretation", core.interpretation);
  add("technical_internal_limitation", core.technical_internal_limitation);
  add("honest_scope", core.honest_scope);
  add("project_justification.gap", core.project_justification?.gap);
  add("project_justification.niche", core.project_justification?.niche);
  add("project_justification.fill", core.project_justification?.fill);

  for (const symbol of core.symbols) {
    add(`symbol:${symbol.name}.type`, symbol.type);
    add(`symbol:${symbol.name}.space`, symbol.space);
    add(`symbol:${symbol.name}.sig`, symbol.sig);
    add(`symbol:${symbol.name}.def`, symbol.def);
    add(`symbol:${symbol.name}.role`, symbol.role);
  }
  for (const assumption of core.assumptions) {
    if (assumption.id === opts.excludeNodeId) continue;
    add(`${assumption.id}.condition`, assumption.condition);
    add(`${assumption.id}.novel.justification`, assumption.novel?.justification);
    add(`${assumption.id}.maintained.reason`, assumption.maintained?.reason);
    add(`${assumption.id}.maintained.open_object`, assumption.maintained?.open_object);
    add(`${assumption.id}.maintained.separate_object`, assumption.maintained?.separate_object);
  }
  for (const definition of core.definitions) {
    if (definition.id === opts.excludeNodeId) continue;
    add(`${definition.id}.name`, definition.name);
    add(`${definition.id}.construction`, definition.construction);
    for (let i = 0; i < (definition.by_member_properties ?? []).length; i++) {
      add(`${definition.id}.by_member_properties[${i}]`, definition.by_member_properties![i]);
    }
    for (let i = 0; i < (definition.inputs ?? []).length; i++) {
      add(`${definition.id}.inputs[${i}]`, definition.inputs![i]);
    }
  }
  for (const statement of core.statements) {
    if (statement.id === opts.excludeNodeId) continue;
    add(`${statement.id}.statement`, statement.statement);
    add(`${statement.id}.proof_tex`, statement.proof_tex);
    add(`${statement.id}.route`, statement.route);
    add(`${statement.id}.justification`, statement.justification);
    add(`${statement.id}.gap`, statement.gap);
    add(`${statement.id}.consumer`, statement.consumer);
    add(`${statement.id}.source.verbatim_statement`, statement.source?.verbatim_statement);
    add(`${statement.id}.source.attestation.note`, statement.source?.attestation?.note);
  }
  return out;
}
