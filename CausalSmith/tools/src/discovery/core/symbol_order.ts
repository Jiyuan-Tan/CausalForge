import type { CoreSymbol } from "./schema.js";

/** Stable topological order for the declared-symbol subgraph.
 *
 * `refs` may also name primitives outside the table; only edges between declared
 * symbols constrain order. Ties retain author order. A cycle or duplicate name is
 * returned unchanged so the structural gate, rather than a canonicalizer, reports it.
 */
export function topologicallyOrderSymbols(symbols: CoreSymbol[]): CoreSymbol[] {
  const byName = new Map<string, CoreSymbol>();
  const index = new Map<string, number>();
  for (const [i, symbol] of symbols.entries()) {
    if (byName.has(symbol.name)) return symbols;
    byName.set(symbol.name, symbol);
    index.set(symbol.name, i);
  }
  const indegree = new Map<string, number>(symbols.map((symbol) => [symbol.name, 0]));
  const dependents = new Map<string, Set<string>>();
  for (const symbol of symbols) {
    for (const ref of new Set(symbol.refs ?? [])) {
      if (!byName.has(ref)) continue;
      indegree.set(symbol.name, (indegree.get(symbol.name) ?? 0) + 1);
      const children = dependents.get(ref) ?? new Set<string>();
      children.add(symbol.name);
      dependents.set(ref, children);
    }
  }
  const ready = symbols.filter((symbol) => indegree.get(symbol.name) === 0);
  const ordered: CoreSymbol[] = [];
  while (ready.length > 0) {
    ready.sort((a, b) => index.get(a.name)! - index.get(b.name)!);
    const symbol = ready.shift()!;
    ordered.push(symbol);
    for (const child of dependents.get(symbol.name) ?? []) {
      const degree = (indegree.get(child) ?? 0) - 1;
      indegree.set(child, degree);
      if (degree === 0) ready.push(byName.get(child)!);
    }
  }
  return ordered.length === symbols.length ? ordered : symbols;
}
