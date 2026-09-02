/** Q→T edge normalization shared by merge (records) and assemble (render).
 *
 * Once an open-ended question Q is resolved by an answer theorem T, every
 * dependency on Q denotes T. The one exception is T's own citation of the
 * question it settles: mapping it to T manufactures a self-cycle and keeping
 * the raw id leaves a dangling edge once Q leaves the render (G4 either way).
 * That edge is replaced by Q's own upstream dependencies, so the answer still
 * reaches the assumptions the question was posed under. Duplicates are removed,
 * order preserved. */
export function remapResolvedDependencies(
  consumerId: string,
  dependencies: readonly string[],
  replacement: ReadonlyMap<string, string>,
  questionDependencies: (questionId: string) => readonly string[] | undefined,
): string[] {
  const out: string[] = [];
  const push = (id: string): void => {
    if (id !== consumerId && !out.includes(id)) out.push(id);
  };
  for (const dependency of dependencies) {
    const target = replacement.get(dependency);
    if (target === undefined) push(dependency);
    else if (target !== consumerId) push(target);
    else {
      for (const inherited of questionDependencies(dependency) ?? []) {
        const mapped = replacement.get(inherited) ?? inherited;
        push(mapped);
      }
    }
  }
  return out;
}

/** Edge rewrite for a `statement-delete`. Without a replacement the edge is
 * dropped; with one it denotes the replacement, except the replacement's own
 * citation of the node it supersedes (the usual "derived from the old result"
 * shape), which is dropped rather than turned into a self-edge that G4 rejects
 * and that would discard the round on every replay of the sealed mandate. */
export function retargetDeletedDependency(
  consumerId: string,
  dependencies: readonly string[],
  deletedId: string,
  replacementId: string | undefined,
): string[] {
  const out: string[] = [];
  for (const dependency of dependencies) {
    const mapped = dependency === deletedId ? replacementId : dependency;
    if (mapped === undefined || mapped === consumerId || out.includes(mapped)) continue;
    out.push(mapped);
  }
  return out;
}
