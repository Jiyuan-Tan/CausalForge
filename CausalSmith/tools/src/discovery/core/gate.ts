// The D0 structural gate (CausalSmith/doc/research/D0_CORE_REDESIGN.md §4).
//
// Mechanical, no LLM. Runs on the core right after D0-CORE (and on the proto_core
// subset at D-1). A whole class of discovery-layer defects never reaches an LLM
// reviewer. Checks G1–G7; returns every violation with its gate code + location.
import { CoreSchema, type Core } from "./schema.js";
import { nodeRefRegex } from "./node_ids.js";

export interface GateViolation {
  code: "schema" | "G1" | "G2" | "G3" | "G4" | "G5" | "G6" | "G7";
  where: string;
  message: string;
}

export interface GateResult {
  ok: boolean;
  violations: GateViolation[];
}

export interface GateOptions {
  /** At the post-PROVE "core" phase, every statement must be discharged
   * (status === "proved"). At D-1/proto and post-CORE phases, leave false. */
  requireDischarged?: boolean;
}

// G2: an assumption.condition is a SINGLE pure relation. These tokens mark
// derived consequences, where-used pointers, disclaimers, or meta-prose. Do not
// ban adjectives used inside legitimate named mathematical conditions (for
// example, "standard Borel"); the standard/novel metadata checks provenance.
const BANNED_TOKENS: RegExp[] = [
  /\bthus\b/i,
  /\bconsequently\b/i,
  /\bhence\b/i,
  /\bmoreover\b/i,
  /\bin addition\b/i,
  /\b(and )?likewise\b/i,
  /\bis used (by|for|in)\b/i,
  /\bused (by|for|in) the\b/i,
  /\bwe assume\b/i,
  /\bno .* is claimed\b/i,
];

// Provability-commentary forbidden in a frozen definition's `construction` (G7
// provability firewall). Targets editorializing phrases only — NOT bare "open"
// (legitimate in "open interval/ball"), so a real construction formula is safe.
const PROVABILITY_COMMENTARY: RegExp[] = [
  /\bleft open\b/i,
  /\bremains? open\b/i,
  /\bopen (problem|question)\b/i,
  /\bnot derivable\b/i,
  /\bun-?derivable\b/i,
  /\bcannot be (derived|determined|fixed|proven|established|pinned)\b/i,
  /\bnot (fixed|determined|derived|pinned) by the [^.]{0,30}primitives\b/i,
  /\bunprovable\b/i,
];

function escapeRe(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

/** Mechanical dead-assumption prune (D-stage). An assumption referenced by NO
 *  statement — directly in a `depends_on`, transitively through the statement
 *  dependency chain, or as a class `by_member_properties` member — is an isolated,
 *  unused block: it belongs to no result and only widens the faithfulness surface
 *  (a hypothesis nothing constrains, so its Lean encoding is never checked against a
 *  proof). Remove it. Statements (the deliverables) and definitions (construction
 *  primitives) are never pruned. Deterministic, no LLM. Returns the pruned core and
 *  the removed assumption ids. */
export function pruneDeadAssumptions(coreInput: unknown): { core: Core; pruned: string[] } | null {
  const parsed = CoreSchema.safeParse(coreInput);
  if (!parsed.success) return null;
  const core = parsed.data;
  const stmtById = new Map(core.statements.map((s) => [s.id, s] as const));
  const classMembers = new Map(core.definitions.map((d) => [d.id, d.by_member_properties ?? []] as const));
  const defById = new Map(core.definitions.map((d) => [d.id, d] as const));
  // Aliveness closure rooted at the statements (every theorem/lemma/OEQ is a deliverable).
  const alive = new Set<string>();
  // Seed with DEFINITIONS as well as statements. Definitions are never pruned, so one
  // that survives can still reference an assumption through `by_member_properties` — but
  // its members were only reached if some statement happened to depend_on that definition.
  // A class definition nothing depends on therefore had its assumptions pruned out from
  // under it, leaving the class defined by a property that no longer exists. Surfaced
  // 2026-07-20 while testing a gate check for exactly that dangling reference.
  const stack: string[] = [...core.statements.map((s) => s.id), ...core.definitions.map((d) => d.id)];
  const REF_RE = nodeRefRegex(); // shared definition — see core/node_ids.ts
  while (stack.length) {
    const id = stack.pop()!;
    if (alive.has(id)) continue;
    alive.add(id);
    const s = stmtById.get(id);
    for (const d of s?.depends_on ?? []) stack.push(d);
    for (const m of classMembers.get(id) ?? []) stack.push(m);
    // A definition also references assumptions through `inputs` and its `construction`
    // prose. Following only `by_member_properties` meant a CONSTRUCTED definition (which
    // has no member properties) kept its identity while an assumption it consumes was
    // pruned out from under it.
    const def = defById.get(id);
    if (def) {
      for (const r of def.inputs ?? []) stack.push(r);
      for (const m of `${def.construction ?? ""}`.matchAll(REF_RE)) stack.push(m[0].toLowerCase());
    }
    // Also keep alive anything the node CITES in its proof/statement prose: the solver's
    // `depends_on` is not always complete vs. its `Ass:`/`Lem:` prose, so an assumption used
    // in a proof but absent from depends_on would be pruned here and then trip the D0
    // consistency gate (dangling citation). Mirrors the reachability fix in
    // stage0_working.pruneOrphanLemmas; a truly-unused assumption (cited nowhere) is still pruned.
    if (s) {
      const prose = `${s.proof_tex ?? ""} ${s.statement ?? ""}`;
      for (const m of prose.matchAll(REF_RE)) stack.push(m[0].toLowerCase());
    }
  }
  const pruned: string[] = [];
  core.assumptions = core.assumptions.filter((a) => {
    if (alive.has(a.id)) return true;
    pruned.push(a.id);
    return false;
  });
  return { core, pruned };
}

export function runStructuralGate(coreInput: unknown, opts: GateOptions = {}): GateResult {
  const violations: GateViolation[] = [];

  const parsed = CoreSchema.safeParse(coreInput);
  if (!parsed.success) {
    for (const issue of parsed.error.issues) {
      violations.push({
        code: "schema",
        where: issue.path.join(".") || "<root>",
        message: issue.message,
      });
    }
    return { ok: false, violations };
  }
  const core = parsed.data;

  const symbolNames = new Set(core.symbols.map((s) => s.name));
  const classDefs = core.definitions.filter((d) => d.by_member_properties !== undefined);
  const constructionDefs = core.definitions.filter((d) => d.by_member_properties === undefined);
  const classNames = classDefs.map((d) => d.name);
  const constructionNames = constructionDefs.map((d) => d.name);
  const nodeIds = new Set<string>([
    ...core.assumptions.map((a) => a.id),
    ...core.definitions.map((d) => d.id),
    ...core.statements.map((s) => s.id),
  ]);
  const bibKeys = new Set(core.bibliography.map((b) => b.key));

  // G1: every declared free symbol is in the symbol table; symbol def-refs are
  // defined before use (array order is the definition order).
  for (const a of core.assumptions) {
    for (const fs of a.free_symbols) {
      if (!symbolNames.has(fs)) {
        violations.push({
          code: "G1",
          where: a.id,
          message:
            `free symbol '${fs}' not in symbol table; each free_symbols element must name ` +
            `exactly one declared symbol (split comma-separated groups)`,
        });
      }
    }
  }
  const seenSymbols = new Set<string>();
  for (const s of core.symbols) {
    for (const r of s.refs ?? []) {
      if (symbolNames.has(r) && !seenSymbols.has(r)) {
        violations.push({
          code: "G1",
          where: `symbol:${s.name}`,
          message: `references symbol '${r}' before it is defined`,
        });
      }
    }
    seenSymbols.add(s.name);
  }

  // G2: single relation, no forbidden prose.
  for (const a of core.assumptions) {
    for (const re of BANNED_TOKENS) {
      if (re.test(a.condition)) {
        violations.push({
          code: "G2",
          where: a.id,
          message: `condition contains forbidden prose (${re.source})`,
        });
      }
    }
    const clauses = a.condition.split(/\.\s+(?=[A-Z(\\])/).filter((x) => x.trim().length > 0);
    if (clauses.length > 1) {
      violations.push({
        code: "G2",
        where: a.id,
        message: `condition reads as ${clauses.length} sentences (omnibus?) — split into atomic conditions`,
      });
    }
  }

  // G3: no assumption asserts membership in a CLASS (A6). Class membership of a
  // construction is always a statement, never an assumption.
  for (const a of core.assumptions) {
    for (const cn of classNames) {
      const re = new RegExp(`(∈|\\\\in|belongs to|lies in)\\s*\\$?${escapeRe(cn)}`, "i");
      if (re.test(a.condition)) {
        violations.push({
          code: "G3",
          where: a.id,
          message: `assumption asserts membership in class '${cn}' — must be a derived statement, not an assumption`,
        });
      }
    }
  }

  // G4: deps exist; statement DAG acyclic; (optionally) all discharged.
  for (const s of core.statements) {
    for (const d of s.depends_on) {
      if (!nodeIds.has(d)) {
        violations.push({ code: "G4", where: s.id, message: `depends_on '${d}' does not exist` });
      }
    }
  }
  const stmtIds = new Set(core.statements.map((s) => s.id));
  const adj = new Map<string, string[]>();
  for (const s of core.statements) {
    adj.set(
      s.id,
      s.depends_on.filter((d) => stmtIds.has(d)),
    );
  }
  const color = new Map<string, number>(); // 0 unvisited, 1 in-stack, 2 done
  const cycleAt = (start: string): string | null => {
    const stack: string[] = [start];
    const path: string[] = [];
    const localDfs = (u: string): string | null => {
      color.set(u, 1);
      path.push(u);
      for (const v of adj.get(u) ?? []) {
        const c = color.get(v) ?? 0;
        if (c === 1) return v;
        if (c === 0) {
          const hit = localDfs(v);
          if (hit) return hit;
        }
      }
      color.set(u, 2);
      path.pop();
      return null;
    };
    void stack;
    return localDfs(start);
  };
  for (const s of core.statements) {
    if ((color.get(s.id) ?? 0) === 0) {
      const hit = cycleAt(s.id);
      if (hit) {
        violations.push({ code: "G4", where: s.id, message: `dependency cycle reaches '${hit}'` });
        break;
      }
    }
  }
  if (opts.requireDischarged) {
    for (const s of core.statements) {
      // An OPEN-ENDED QUESTION may be a LEGITIMATELY OPEN residual (a tightness / matching
      // question the note poses but does not resolve). Whether an open OEQ is an acceptable
      // residual is a D0.5 TIERING decision, not a structural-discharge requirement — so do
      // not fail the discharge gate on an unproved OEQ. Theorems/lemmas/props must still be
      // proved.
      if (s.kind === "openendedquestion" && s.id.startsWith("oeq:")) continue; // why: theorem-id nodes must not inherit the OEQ discharge exemption by kind alone.
      // A `cited` statement is DISCHARGED by its citation — it is an invoked classical
      // result, not a leaf we owe a proof for (its source⟺status xor + leaf rule are
      // enforced by the schema, and the bibkey by G6). Requiring `proved` here would
      // force re-deriving a published theorem; treat `cited` as discharged like `proved`.
      if (s.status !== "proved" && s.status !== "cited") {
        violations.push({
          code: "G4",
          where: s.id,
          message: `node left undischarged (status='${s.status}') after PROVE`,
        });
      }
    }
  }

  // G5: a class is carved only by member-properties. Its `construction` is the
  // explicit set-builder (required by the schema), but it must NOT take
  // construction `inputs`, and NEITHER the member-property list NOR the
  // set-builder text may reference a witness construction — that is the A6
  // firewall (carve a class by a membership predicate, never by a witness image).
  for (const d of classDefs) {
    if (d.inputs !== undefined) {
      violations.push({
        code: "G5",
        where: d.id,
        message: `class '${d.name}' must not carry construction inputs — its \`construction\` is the membership set-builder, not a parametrized construction`,
      });
    }
    const witnessSites: Array<[string, string]> = [
      ...(d.by_member_properties ?? []).map((mp) => ["member-property", mp] as [string, string]),
      ["set-builder", d.construction],
    ];
    for (const [site, text] of witnessSites) {
      for (const cn of constructionNames) {
        if (new RegExp(escapeRe(cn)).test(text)) {
          violations.push({
            code: "G5",
            where: d.id,
            message: `class '${d.name}' ${site} references construction '${cn}' — carve a class by a membership predicate, not a witness image`,
          });
        }
      }
    }
  }

  // G6: standard.cite resolves to a bibliography entry (the xor is enforced by
  // the schema refine; this checks the citation is real).
  for (const a of core.assumptions) {
    if (a.standard && !bibKeys.has(a.standard.cite)) {
      violations.push({
        code: "G6",
        where: a.id,
        message: `standard.cite '${a.standard.cite}' not in bibliography`,
      });
    }
  }
  // G6 (cited statements): a `status:"cited"` statement's `source.cite` resolves to
  // a bibliography entry (the cited⟺source xor and the leaf rule are enforced by the
  // schema refine; this checks the citation is real). This is the structured
  // provenance F1 turns into a `cite:` node, so the bibkey must exist.
  for (const s of core.statements) {
    if (s.status === "cited" && s.source && !bibKeys.has(s.source.cite)) {
      violations.push({
        code: "G6",
        where: s.id,
        message: `source.cite '${s.source.cite}' not in bibliography`,
      });
    }
  }

  // G7: a construction definition carries no by_member_properties (the schema
  // refine enforces it; double-check for robustness if the schema is loosened).
  for (const d of constructionDefs) {
    if (d.by_member_properties !== undefined) {
      violations.push({
        code: "G7",
        where: d.id,
        message: `construction '${d.name}' must not carry by_member_properties`,
      });
    }
  }

  // G7 (provability firewall): a frozen definition NAMES a construction or fixes
  // a quantity — it must NEVER editorialize about whether a target is provable.
  // A def asserting "left open / not derivable / not fixed by the primitives" is a
  // self-fulfilling prophecy: the solver respects the frozen core and dutifully
  // reports the target open. The freeze binds the QUESTION, never the answer's
  // existence. Strip such commentary at the discovery layer.
  for (const d of core.definitions) {
    for (const re of PROVABILITY_COMMENTARY) {
      if (re.test(d.construction)) {
        violations.push({
          code: "G7",
          where: d.id,
          message: `definition '${d.name}' \`construction\` editorializes about provability (${re.source}) — a frozen def names a construction or fixes a quantity, it must not assert a target is open/underivable; the solver derives the answer`,
        });
      }
    }
  }

  return { ok: violations.length === 0, violations };
}
