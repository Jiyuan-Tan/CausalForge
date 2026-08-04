import type { CoreDefinition } from "./schema.js";
import { extractNodeRefs } from "./node_ids.js";

/** Stable topological order for definition-to-definition references.
 *
 * Constructed definitions may name earlier definitions through `inputs` or
 * literal `def:` references in their construction. New definitions are appended
 * by the edit channel, so canonicalize the accepted post-image mechanically.
 * Ties retain author order; duplicates or cycles fail closed.
 */
export function topologicallyOrderDefinitions(definitions: CoreDefinition[]): CoreDefinition[] {
  const byId = new Map<string, CoreDefinition>();
  const index = new Map<string, number>();
  for (const [i, definition] of definitions.entries()) {
    if (byId.has(definition.id)) {
      throw new Error(`Cannot order duplicate definition id ${definition.id}`);
    }
    byId.set(definition.id, definition);
    index.set(definition.id, i);
  }

  const indegree = new Map<string, number>(definitions.map((definition) => [definition.id, 0]));
  const dependents = new Map<string, Set<string>>();
  for (const definition of definitions) {
    const refs = new Set<string>([
      ...(definition.inputs ?? []).filter((input) => input.startsWith("def:")),
      ...extractNodeRefs(`${definition.construction}\n${(definition.inputs ?? []).join("\n")}`)
        .filter((id) => id.startsWith("def:")),
    ]);
    for (const ref of refs) {
      if (!byId.has(ref)) continue;
      indegree.set(definition.id, (indegree.get(definition.id) ?? 0) + 1);
      const children = dependents.get(ref) ?? new Set<string>();
      children.add(definition.id);
      dependents.set(ref, children);
    }
  }

  const ready = definitions.filter((definition) => indegree.get(definition.id) === 0);
  const ordered: CoreDefinition[] = [];
  while (ready.length > 0) {
    ready.sort((a, b) => index.get(a.id)! - index.get(b.id)!);
    const definition = ready.shift()!;
    ordered.push(definition);
    for (const child of dependents.get(definition.id) ?? []) {
      const degree = (indegree.get(child) ?? 0) - 1;
      indegree.set(child, degree);
      if (degree === 0) ready.push(byId.get(child)!);
    }
  }
  if (ordered.length !== definitions.length) {
    const cyclic = definitions
      .filter((definition) => (indegree.get(definition.id) ?? 0) > 0)
      .map((definition) => definition.id);
    throw new Error(`Cannot order cyclic definition dependencies: ${cyclic.join(", ")}`);
  }
  return ordered;
}
