#!/usr/bin/env node
/** One-off audited migration for legacy D0 cores that proved OEQs in place. */
import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { CoreSchema } from "../../src/discovery/core/schema.js";
import { PlanSchema } from "../../src/formalization/plan/schema.js";
import { runPlanGate } from "../../src/formalization/plan/plan_gate.js";
import { buildGraphFromCorePlan } from "../../src/graph/from_core.js";

type Resolution = {
  source_id: string;
  theorem: { id: string; statement: string; lean_name: string };
};

const manifests: Record<string, Resolution[]> = {
  eid_lingam_direction_min_order_v1: [
    {
      source_id: "oeq:generic-separation",
      theorem: {
        id: "thm:generic-arrow-recovery-and-fiber-obstruction",
        lean_name: "genericArrowRecoveryAndFiberObstruction",
        statement: "For every m >= 1 at K = 2m+2, there are Zariski-open dense loci meeting the real feasible regions on which the loading direction is recovered and no full opposite-arrow fiber exists. However, the same-arrow fiber is not a single G_m-orbit: an omitted source-pair permutation already gives multiple orbits, and for m >= 2 every generic fiber has dimension m(m-1)/2 from the low-order weight kernels.",
      },
    },
    {
      source_id: "oeq:generic-exceptional-locus",
      theorem: {
        id: "thm:exceptional-locus-codimension-one",
        lean_name: "exceptionalLocusCodimensionOne",
        statement: "For every m >= 1 at K = 2m+2, the complex exceptional closure barE_m has codimension one in each arrow-image variety, not codimension m when m >= 2. Its two generic parameter preimages are exactly the points retaining a full opposite-arrow representation, and the full-fiber polynomial incidence equations specialize explicitly at m = 1, K = 4 and m = 2, K = 6.",
      },
    },
    {
      source_id: "oeq:minimal-real-information-order",
      theorem: {
        id: "thm:improved-real-information-order",
        lean_name: "improvedRealInformationOrder",
        statement: "For every m >= 3, generic real arrow recovery already holds from cumulants through order 2m+1, so K^star(m) <= 2m+1. Consequently the proposed identity K^star(m) = 2m+2 for every m >= 1 is false.",
      },
    },
    {
      source_id: "oeq:real-exceptional-atlas",
      theorem: {
        id: "thm:exact-real-exceptional-atlas",
        lean_name: "exactRealExceptionalAtlas",
        statement: "For every fixed m, there is a finite computable semialgebraic cylindrical atlas of the real exceptional closure such that, on each base cell, the complete feasible forward and reverse fibers are finite unions of recursively cylindrical section and sector cells and their nonemptiness labels are constant. The atlas includes singular and nongeneric boundary branches and decides exactly when both real arrows are feasible.",
      },
    },
  ],
  exp_bipartite_minimax_design: [
    {
      source_id: "oeq:dispersion-certificate",
      theorem: {
        id: "thm:dispersion-certificate-unbounded",
        lean_name: "dispersionCertificateUnbounded",
        statement: "For every epsilon in (0,1/2), every c_disp > 0, and every C_disp >= 1, there is a sequence of finite bipartite graphs satisfying the stated positive-energy, degree-dispersion, and h-weight-ratio bounds for which alpha_cert(G_n) tends to infinity. Thus those first-order dispersion summaries do not uniformly bound the surrogate approximation ratio.",
      },
    },
  ],
  stat_dose_response_minimax: [
    {
      source_id: "oeq:full-beta-frontier",
      theorem: {
        id: "thm:certified-partial-beta-frontier",
        lean_name: "certifiedPartialBetaFrontier",
        statement: "Under baseline-submodel slack, for every fixed beta > 0 the original dose-response class has minimax MSE at least c n^(-2 alpha/(2 alpha+1)) for all sufficiently large n. This lower floor matches the published rho_n exponent when s >= d/4; when 0 < s < d/4, rho_n has a strictly smaller exponent and remains only an upper-side comparator, so no same-class upper endpoint is asserted.",
      },
    },
  ],
};

const root = path.resolve(import.meta.dirname, "../../..");

for (const [run, resolutions] of Object.entries(manifests)) {
  const runDir = path.join(root, "doc/research", run);
  const corePath = path.join(runDir, "discovery/core.json");
  const planPath = path.join(runDir, "formalization/plan.json");
  const statePath = path.join(runDir, "state.json");
  const core = JSON.parse(await readFile(corePath, "utf8"));
  const plan = JSON.parse(await readFile(planPath, "utf8"));
  const state = JSON.parse(await readFile(statePath, "utf8"));
  const remap = new Map(resolutions.map((r) => [r.source_id, r.theorem.id]));
  const emitted: unknown[] = [];

  for (const r of resolutions) {
    let index = core.statements.findIndex((s: any) => s.id === r.source_id);
    let theorem: any;
    if (index >= 0) {
      const source = core.statements[index];
      if (source.kind !== "openendedquestion" || source.status !== "proved" || !source.proof_tex?.trim()) {
        throw new Error(`${run}: ${r.source_id} is not a proved OEQ with proof text`);
      }
      theorem = {
        ...source,
        id: r.theorem.id,
        kind: "theorem",
        statement: r.theorem.statement,
        status: "proved",
      };
      core.statements[index] = theorem;
    } else {
      index = core.statements.findIndex((s: any) => s.id === r.theorem.id);
      if (index < 0) throw new Error(`${run}: missing ${r.source_id} and ${r.theorem.id}`);
      theorem = core.statements[index];
    }
    emitted.push({ source_id: r.source_id, theorem });

    const prior = plan.nodes[r.source_id] ?? plan.nodes[r.theorem.id];
    if (!prior) throw new Error(`${run}: plan is missing ${r.source_id}`);
    delete plan.nodes[r.source_id];
    plan.nodes[r.theorem.id] = {
      ...prior,
      lean_kind: "theorem",
      lean_name: r.theorem.lean_name,
      disposition: "define-local",
      defer_tier: false,
      gate: false,
      local_id: r.theorem.id,
      notes: `MANUAL D0 SALVAGE: ${r.source_id} was proved in place by the legacy solver. It is replaced by ${r.theorem.id}; formalize the proved answer in core.json, not the obsolete interrogative proposition.`,
    };
  }

  for (const s of core.statements) {
    s.depends_on = (s.depends_on ?? []).map((id: string) => remap.get(id) ?? id);
  }
  for (const n of Object.values(plan.nodes) as any[]) {
    if (Array.isArray(n.hyps)) n.hyps = n.hyps.map((id: string) => remap.get(id) ?? id);
  }

  await writeFile(corePath, JSON.stringify(core, null, 2) + "\n");
  await writeFile(planPath, JSON.stringify(plan, null, 2) + "\n");
  const salvageDirective = [
    "MANUAL RESOLVED-OEQ SALVAGE (authoritative for this F2 rewind):",
    ...resolutions.map((r) => `- ${r.source_id} was removed and replaced by proved ${r.theorem.id}; emit a theorem named ${r.theorem.lean_name} from the answer statement and proof in discovery/core.json.`),
    "Any legacy formalization.md prose that still presents one of those nodes as an open question is superseded by core.json and plan.json. Do not recreate an oeq: Prop def.",
  ].join("\n");
  state.flags ??= {};
  const priorDirective = String(state.flags.f2_scaffold_directive ?? "");
  const marker = "MANUAL RESOLVED-OEQ SALVAGE (authoritative for this F2 rewind):";
  state.flags.f2_scaffold_directive = priorDirective.includes(marker)
    ? priorDirective.slice(0, priorDirective.indexOf(marker)).trimEnd() + (priorDirective.slice(0, priorDirective.indexOf(marker)).trim() ? "\n\n" : "") + salvageDirective
    : [priorDirective.trim(), salvageDirective].filter(Boolean).join("\n\n");
  await writeFile(statePath, JSON.stringify(state, null, 2) + "\n");
  await writeFile(
    path.join(runDir, "discovery/resolved_oeqs_manual.json"),
    JSON.stringify({ resolved_oeqs: emitted }, null, 2) + "\n",
  );
  const parsedCore = CoreSchema.parse(core);
  const parsedPlan = PlanSchema.parse(plan);
  const gate = runPlanGate(parsedPlan, parsedCore);
  const migratedIds = new Set(resolutions.map((r) => r.theorem.id));
  const migrationViolations = gate.violations.filter((v) => migratedIds.has(v.where));
  if (migrationViolations.length > 0) {
    throw new Error(`${run}: migrated OEQ entries failed plan gate: ${migrationViolations.map((v) => `${v.code} ${v.where}: ${v.message}`).join("; ")}`);
  }
  const graph = buildGraphFromCorePlan(parsedCore, parsedCore.specialization ?? "", parsedPlan);
  await writeFile(path.join(runDir, "graph.json"), JSON.stringify(graph, null, 2) + "\n");
  process.stdout.write(`${run}: migrated ${resolutions.length} resolved OEQ(s)\n`);
}
