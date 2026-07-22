import { z } from "zod";

export const NODE_KINDS = ["setup", "definition", "assumption", "lemma", "theorem", "gate"] as const;
export type NodeKind = (typeof NODE_KINDS)[number];

export const PROVENANCES = ["from-note", "agent-introduced", "library"] as const;
export type Provenance = (typeof PROVENANCES)[number];

export const REVIEW_STATUSES = ["unreviewed", "matched", "derived", "drift"] as const;
export type ReviewStatus = (typeof REVIEW_STATUSES)[number];

export const PROOF_STATES = ["complete", "sorry", "error"] as const;
export type ProofState = (typeof PROOF_STATES)[number];

export const ASSUMPTION_CLASSES = [
  "faithful-refinement",
  "regularity-bookkeeping",
  "substrate-gate",
] as const;
export type AssumptionClass = (typeof ASSUMPTION_CLASSES)[number];

export const EDGE_KINDS = ["statement-uses", "proof-uses", "setup-of"] as const;
export type EdgeKind = (typeof EDGE_KINDS)[number];

export const EDGE_SOURCES = ["extracted", "declared"] as const;
export type EdgeSource = (typeof EDGE_SOURCES)[number];

const NlSchema = z.object({
  statement: z.string(),
  tex_anchor: z.string(),
  frozen: z.boolean(),
  // A P3-validated frozen environment, persisted so a P1 re-run reproduces it VERBATIM instead of
  // re-deriving from `statement` (often a loose "headline") and reverting the tightening P3 already
  // reconciled to Lean. `frozen_body` is the LaTeX between \begin/\end; `frozen_title` the optional
  // env title. Written by P3's equivalence gate the moment a refinement reaches faithful; consumed
  // by P1, which renders the rest of the layer but leaves these locked. Absent ⇒ normal render.
  frozen_body: z.string().optional(),
  frozen_title: z.string().nullable().optional(),
});

const LeanSchema = z.object({
  decl_name: z.string().nullable(),
  file: z.string().nullable(),
});

const ReviewSchema = z.object({
  status: z.enum(REVIEW_STATUSES),
  passed_hash: z.string().nullable(),
  /** The reviewer's one-line reason for the current verdict (esp. why a `drift`). Persisted so
   *  an escalation surfaces WHICH hypothesis/term diverged, not just that the node is flagged. */
  note: z.string().optional(),
});

const ProofSchema = z.object({
  state: z.enum(PROOF_STATES),
  sorry_count: z.number().int().nonnegative(),
});

const DeliverySchema = z.object({
  role: z.enum(["headline", "headline-support", "secondary"]).optional(),
  status: z.enum(["deliver", "undelivered"]),
  reason: z.string().min(1).optional(),
});

export const NodeSchema = z.object({
  id: z.string().min(1),
  /** CausalSmith-present-compatible obj-id alias (`P-1` / `T-1` / `L-1` / `A-1` / `S-1`),
   *  stamped by `buildGraphFromCorePlan` so a core-keyed graph (`id = thm:foo`) still
   *  correlates with a `parseNoteBlocks`-keyed bridge note. Absent on legacy md-built
   *  graphs (whose `id` already IS the obj-id-derived form). */
  obj_id: z.string().optional(),
  kind: z.enum(NODE_KINDS),
  provenance: z.enum(PROVENANCES),
  nl: NlSchema,
  lean: LeanSchema,
  review: ReviewSchema,
  proof: ProofSchema,
  delivery: DeliverySchema.optional(),
  assumption: z
    .object({
      tier: z.union([z.literal(1), z.literal(2)]),
      classification: z.enum(ASSUMPTION_CLASSES),
    })
    .optional(),
  /** Citation provenance for a `from-note` ASSUMPTION, carried from the typed core's
   *  `assumptions[*].standard` ({name, cite}) plus the matching `bibliography` entry's free
   *  text (`citation`). Present iff the core marked the assumption as a STANDARD named
   *  condition (absent ⇒ novel to this work). CausalSmith present P2 uses it to gloss each assumption
   *  ("the standard <name> condition, <cite>"); `cite` is the core/discovery bib key and
   *  `citation` lets the emitter reconcile it to the paper's own references.bib key. */
  standard: z
    .object({ name: z.string(), cite: z.string(), citation: z.string().optional() })
    .optional(),
  /** For a `kind:"gate"` node: its discharge fate and (for cited) the citation it is
   *  matched against, carried from the plan node's `gate_class`/`source`. `gated` =
   *  discharged before banking; `cited` = borrowed, assumed + source-matched. Absent
   *  ⇒ legacy gate (treat as `gated`). Lets graph-based logic distinguish the two
   *  without re-reading plan.json. */
  gate: z
    .object({
      gate_class: z.enum(["gated", "cited"]).optional(),
      source: z.string().optional(), // the `cite:` node id this gate is matched against
    })
    .optional(),
  setup: z.object({ required_modules: z.array(z.string()) }).optional(),
});
export type GraphNode = z.infer<typeof NodeSchema>;

export function isUndeliveredNode(n: GraphNode): boolean {
  return n.delivery?.status === "undelivered";
}

export const EdgeSchema = z.object({
  kind: z.enum(EDGE_KINDS),
  from: z.string().min(1),
  to: z.string().min(1),
  source: z.enum(EDGE_SOURCES),
});
export type GraphEdge = z.infer<typeof EdgeSchema>;

export const GraphSchema = z
  .object({
    qid: z.string().min(1),
    specialization: z.string().min(1),
    nodes: z.array(NodeSchema),
    edges: z.array(EdgeSchema),
    /** Incremental review state for SETUP/ENVIRONMENT symbol clusters (`sym:<symbol>`), which are
     *  NOT graph nodes and so have no `node.review` to carry status. Keyed `sym:<symbol>` →
     *  {verdict, hash}: the last reviewer verdict and a hash of the symbol's `@realizes` cluster.
     *  A delta pass skips a symbol whose cluster hash is UNCHANGED and last verdict PASSED (matched /
     *  untagged) — mirroring node-level incrementality; a re-tagged symbol (cluster changed → hash
     *  changed) re-reviews. Convergence (F4) ignores this and re-verifies every symbol. */
    symbolReview: z
      .record(z.string(), z.object({ verdict: z.string(), hash: z.string() }))
      .optional(),
  })
  .superRefine((graph, ctx) => {
    // why: duplicate ids/triples parse as arrays but desync graph lookups later.
    const seenNodes = new Map<string, number>();
    graph.nodes.forEach((n, i) => {
      const first = seenNodes.get(n.id);
      if (first !== undefined) {
        ctx.addIssue({
          code: z.ZodIssueCode.custom,
          path: ["nodes", i, "id"],
          message: `duplicate node id ${n.id} also appears at nodes[${first}]`,
        });
      } else {
        seenNodes.set(n.id, i);
      }
      if (isUndeliveredNode(n)) {
        const cited = n.kind === "gate" && n.gate?.gate_class === "cited";
        const secondaryTheorem = n.kind === "theorem" && n.delivery?.role === "secondary";
        if (!cited && !secondaryTheorem) {
          ctx.addIssue({
            code: z.ZodIssueCode.custom,
            path: ["nodes", i, "delivery"],
            message: "undelivered is legal only for a secondary theorem or a cited gate",
          });
        }
        if (!n.delivery?.reason) {
          ctx.addIssue({
            code: z.ZodIssueCode.custom,
            path: ["nodes", i, "delivery", "reason"],
            message: "undelivered node must disclose a reason",
          });
        }
      }
    });
    const seenEdges = new Map<string, number>();
    graph.edges.forEach((e, i) => {
      const key = `${e.kind}:${e.from}->${e.to}`;
      const first = seenEdges.get(key);
      if (first !== undefined) {
        ctx.addIssue({
          code: z.ZodIssueCode.custom,
          path: ["edges", i],
          message: `duplicate edge ${key} also appears at edges[${first}]`,
        });
      } else {
        seenEdges.set(key, i);
      }
    });
    const byId = new Map(graph.nodes.map((n) => [n.id, n] as const));
    const adj = new Map<string, string[]>();
    for (const e of graph.edges) {
      if (e.kind !== "statement-uses" && e.kind !== "proof-uses") continue;
      const xs = adj.get(e.from) ?? [];
      xs.push(e.to);
      adj.set(e.from, xs);
    }
    for (const from of graph.nodes) {
      if (isUndeliveredNode(from) || (from.kind !== "theorem" && from.kind !== "lemma")) continue;
      const seen = new Set<string>();
      const stack = [...(adj.get(from.id) ?? [])];
      while (stack.length > 0) {
        const id = stack.pop()!;
        if (seen.has(id)) continue;
        seen.add(id);
        const to = byId.get(id);
        if (to && isUndeliveredNode(to)) {
          ctx.addIssue({
            code: z.ZodIssueCode.custom,
            path: ["edges"],
            message: `delivered result ${from.id} transitively depends on undelivered node ${to.id}`,
          });
          break;
        }
        stack.push(...(adj.get(id) ?? []));
      }
    }
  });
export type FormalizationGraph = z.infer<typeof GraphSchema>;

export type FindingSeverity = "error" | "warn";
export interface Finding {
  invariant: string;
  severity: FindingSeverity;
  node?: string;
  message: string;
}
export interface ValidationResult {
  ok: boolean;
  findings: Finding[];
}
