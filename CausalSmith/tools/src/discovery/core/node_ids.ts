// One definition of "a core node reference in prose".
//
// There were four divergent copies of this regex, and the divergence was not
// cosmetic — it produced phantom defects that cost real rounds:
//
//   dependencies.ts / stage0_solve.ts   /\b(?:lem|def|ass|thm|prop|conj):[a-z0-9-]+/g
//   stage0_working.ts / core/gate.ts    /\b(?:ass|def|lem|thm|prop|oeq|conj):[a-z0-9-]+/gi
//
// The first pair lacks `oeq` and the `i` flag, so proof prose citing `oeq:foo` or
// `Lem:bar` was never auto-wired into `depends_on`. The second pair DOES match those,
// then compares them against core ids — so the very citation the wiring ignored is
// reported as a DANGLING citation, which drives the auto-heal / halt branch in
// stage0_typed. A formatting difference in prose thereby presented as a structural
// defect in the paper.
//
// NOTE ON `_`: the character class deliberately matches `core/schema.ts`'s id grammar
// (`[a-z0-9-]+`) and does NOT include `_`. Widening it to `[a-z0-9_-]+` looks like a
// robustness win — it stops `lem:foo_bar` truncating to `lem:foo` — but since no legal
// core id can contain `_`, the widened token can never match anything. It can only
// LOSE a reference that previously resolved, and three consumers treat a lost reference
// as a hard signal: `pruneOrphanLemmas` DELETES a lemma whose last inbound prose edge
// disappears, `pruneDeadAssumptions` does the same for assumptions, and
// `findDanglingCitations` reports the ref as dangling and drives the auto-heal/halt
// branch. On an existing core that is a live-node deletion, so: keep the grammar.

// TWO SEMANTICS, DELIBERATELY DIFFERENT — see `extractCitationRefs` below.
//
// A node id can appear in prose in two ways, and they mean opposite things:
//
//   lem:foo                      a CITATION — "this core proves lem:foo, I invoke it"
//   other_paper/lem:foo          a MENTION  — "another paper proved lem:foo"
//
// The bare pattern matches both, because `\b` also matches right after `/`. That
// misread cost a run: a comparator node naming its source as
// `stat_cot_observational_efficiency/lem:vanishing-variance-studentization` was
// reported as citing an un-emitted member, the consistency gate invalidated its
// proof, and the theorems depending on it aborted the solve (PIPELINE_NOTES
// 2026-07-18). Naming where an idea came from is not a hole in your proof.
//
// The fix is NOT to narrow the shared pattern: consumers need opposite behaviour.
// `gate.ts`'s aliveness closure and `pruneOrphanLemmas` DELETE a node whose last
// inbound prose edge disappears, so for them a lost reference is a live-node
// deletion — they must keep matching permissively. `findDanglingCitations` HALTS
// the run on a reference it cannot resolve, so for it a spurious reference is a
// phantom defect. Hence: `extractNodeRefs` stays permissive (reachability — never
// loses an edge), `extractCitationRefs` is strict (citations only).

/** Node-kind prefixes that can appear in a core id. Keep in sync with `core/schema.ts`. */
export const NODE_KINDS = ["ass", "def", "lem", "thm", "prop", "oeq", "conj"] as const;

// NOTE ON THE LaTeX HYPHEN ESCAPE: the solver writes ids inside math mode, where a
// bare `-` sets as a minus sign, so it escapes them — `def:beta\text{-}free`. Against
// a slug grammar of `[a-z0-9-]+` the match STOPS at the backslash and yields the
// truncated `def:beta`, which resolves against nothing. That is not a cosmetic misread:
// `findDanglingCitations` halts/auto-heals on an unresolvable ref, so a run reported 24
// dangling citations (`def:holder-class` → `def:holder`, `thm:oracle-high-s` →
// `thm:oracle`), invalidated 15 nodes and paid a full re-solve for prose that was
// correct. Accept the escape as a slug character and normalize it back to `-`, so both
// semantics below see the id the author actually wrote.
const HYPHEN_ESCAPE = String.raw`\\(?:text|mbox)\{-\}|\{-\}`;
const SLUG = String.raw`(?:[a-z0-9-]|${HYPHEN_ESCAPE})+`;

const PATTERN = String.raw`\b(?:${NODE_KINDS.join("|")}):${SLUG}`;

/** A `<paper>/<node-id>` reference to a result in ANOTHER CausalSmith paper. The
 *  paper segment matches the qid grammar (`[a-z0-9_]+`, underscores allowed — qids
 *  use them where node ids do not), and may be LaTeX-escaped as `\_` in prose. */
const QUALIFIED_PATTERN = String.raw`(?:[a-z0-9]|\\?_)+/(?:${NODE_KINDS.join("|")}):${SLUG}`;

/** Undo the LaTeX hyphen escapes accepted by `SLUG`, so an extracted ref compares
 *  equal to the plain-`-` id grammar of `core/schema.ts`. */
function normalizeRef(raw: string): string {
  return raw.replace(new RegExp(HYPHEN_ESCAPE, "gi"), "-").toLowerCase();
}

/** A FRESH matcher for `<paper>/<node-id>` cross-paper references. */
export function qualifiedRefRegex(): RegExp {
  return new RegExp(QUALIFIED_PATTERN, "gi");
}

/**
 * Node ids this prose CITES as members of THIS core — bare ids only.
 *
 * A `<paper>/<node-id>` reference names another paper's result and is excluded: it
 * is a mention, not a citation, and resolving it against this core is a category
 * error. Use this wherever an unresolvable reference is treated as a DEFECT.
 *
 * For reachability/pruning use `extractNodeRefs` instead — it matches both forms,
 * so it can never drop an inbound edge and cause a node to be pruned.
 */
export function extractCitationRefs(text: string): string[] {
  // Blank out qualified references first, so the bare pass cannot see the node
  // segment of `other_paper/lem:foo`. Replacing with same-length padding keeps
  // offsets stable for any future caller that wants match positions.
  const masked = text.replace(qualifiedRefRegex(), (m) => " ".repeat(m.length));
  return extractNodeRefs(masked);
}

/** Kind prefixes valid on a STATEMENT id — `NODE_KINDS` minus `ass`/`def`, which name
 *  assumptions and definitions rather than claims. Mirrors `StatementSchema`'s id
 *  grammar in `core/schema.ts`. */
export const STATEMENT_ID_KINDS = ["thm", "lem", "prop", "oeq", "conj"] as const;

/**
 * Normalize a statement id to the schema grammar `(thm|lem|prop|oeq|conj):[a-z0-9-]+`,
 * or return `null` when the id carries no recognizable statement prefix.
 *
 * This is the auto-heal for the solver's habit of naming an added lemma after a
 * capital-letter symbol (`lem:Ghat-envelope-valid` for an estimator Ĝ_n). It was a
 * FIFTH divergent copy of the prefix list living in `stage0_solve.ts`, and it had
 * drifted the same way the four copies above did: it omitted `oeq`. The consequence
 * was worse than a missed heal — `StatementSchema` ACCEPTS `oeq:`, so a bad-cased
 * `oeq:` id was the one case that could reach the schema unhealed and abort an
 * otherwise-clean discharge on a trivial formatting slip.
 */
export function healStatementId(id: string): string | null {
  const m = new RegExp(String.raw`^(${STATEMENT_ID_KINDS.join("|")}):(.+)$`, "i").exec(id);
  if (!m) return null;
  const slug = m[2]
    .toLowerCase()
    .replace(/[^a-z0-9-]+/g, "-")
    .replace(/^-+|-+$/g, "");
  return `${m[1].toLowerCase()}:${slug}`;
}

/** A FRESH global, case-insensitive matcher. Returns a new object each call because a
 *  `/g` regex carries mutable `lastIndex` — sharing one instance across call sites is
 *  its own class of intermittent bug. */
export function nodeRefRegex(): RegExp {
  return new RegExp(PATTERN, "gi");
}

/** Every core-node reference in `text`, lowercased and de-duplicated, in first-seen
 *  order. Lowercasing matches the id convention enforced by `core/schema.ts`. */
export function extractNodeRefs(text: string): string[] {
  // A LaTeX en-dash range between two ids (`thm:lower--thm:upper`, the standard
  // typesetting of "Theorems 1–2") would otherwise be swallowed as the single
  // unresolvable slug `thm:lower--thm` AND lose the second reference outright —
  // for the pruning consumers that is a live-node deletion. Sever the `--` when
  // a new id begins directly after it (same-length padding keeps offsets stable).
  const severed = text.replace(
    new RegExp(String.raw`--(?=(?:${NODE_KINDS.join("|")}):)`, "gi"),
    "  ",
  );
  const seen = new Set<string>();
  const out: string[] = [];
  for (const m of severed.matchAll(nodeRefRegex())) {
    // No pipeline id ends in `-` (`healStatementId` strips them for statements,
    // and slugs are semantic words everywhere), so a trailing hyphen is
    // punctuation the slug absorbed (`… thm:main-,` or the escaped
    // `lem:a-\text{and}…`) — trim it rather than fail to resolve. KNOWN
    // TRADE-OFF: an `ass:`/`def:` id that literally ends in `-` is schema-legal
    // and would stop resolving here; if a producer ever emits one, forbid it at
    // creation (mirror healStatementId) rather than un-trimming this.
    const ref = normalizeRef(m[0]).replace(/-+$/, "");
    if (!seen.has(ref)) {
      seen.add(ref);
      out.push(ref);
    }
  }
  return out;
}
