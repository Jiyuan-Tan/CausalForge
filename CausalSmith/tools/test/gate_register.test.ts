import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises"; // writeFile used to seed husk shapes
import path from "node:path";
import os from "node:os";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { fileURLToPath } from "node:url";
import { beforeEach, describe, expect, it } from "vitest";
import { createInitialState, loadState, saveState } from "../src/state.js";
import { saveGraph, graphPath } from "../src/graph/store.js";
import { formalizationDir, planPath } from "../src/paths.js";
import type { FormalizationGraph, GraphNode } from "../src/graph/types.js";

const exec = promisify(execFile);
const __TOOLS_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const TSX_CLI = path.resolve(__TOOLS_ROOT, "node_modules", "tsx", "dist", "cli.mjs");
const GATE = path.resolve(__TOOLS_ROOT, "bin", "gate.ts");

const QID = "stat_demo";
const SPEC = "v1";
const CONSUMER = "oeq:feasible-upper";
const GATE_ID = "bochner_integrability_gate";
/** The real shape of the defect: a substrate-gate disclosed in prose, with no node behind it. */
const PROSE_LABEL = "crossfit reductions: 4× Integrable sSup gates";

let repoRoot: string;

const node = (id: string, kind: GraphNode["kind"]): GraphNode => ({
  id,
  kind,
  provenance: "from-note",
  nl: { statement: `${id} statement`, tex_anchor: id, frozen: false },
  lean: { decl_name: `Ns.${id.replace(/[:-]/g, "_")}`, file: "F.lean" },
  review: { status: "matched", passed_hash: "h0" },
  proof: { state: "complete", sorry_count: 0 },
});

function gate(args: string[]): Promise<{ stdout: string; stderr: string }> {
  return exec(TSX_CLI, [GATE, QID, SPEC, ...args], { cwd: repoRoot, env: { ...process.env } });
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "gate-reg-"));
  await writeFile(path.join(repoRoot, "lakefile.toml"), `name = "CausalSmith"\n`);

  const st = createInitialState(QID);
  st.added_assumptions = [
    { label: PROSE_LABEL, statement: "Bochner integrability of the sSup integrands", classification: "substrate-gate" },
  ];
  await saveState(repoRoot, QID, SPEC, st);

  const graph: FormalizationGraph = { qid: QID, specialization: SPEC, nodes: [node(CONSUMER, "theorem")], edges: [] };
  const fdir = formalizationDir(repoRoot, QID);
  await mkdir(fdir, { recursive: true });
  await saveGraph(graphPath(fdir, QID, SPEC), graph);

  const ppath = planPath(repoRoot, QID, SPEC);
  await mkdir(path.dirname(ppath), { recursive: true });
  await writeFile(ppath, JSON.stringify({ nodes: { [CONSUMER]: { lean_kind: "theorem", hyps: [] } } }, null, 2));
});

describe("gate.ts registration of a prose-only substrate-gate", () => {
  // Before minting existed, `gate.ts` exited 1 on a node absent from the graph — so a debt
  // disclosed only in `state.added_assumptions` (what `--audit` calls "prose-only and
  // unenforceable") could never be registered. The only escape from the defect was blocked.
  it("MINTS the missing gate node, threads consumers, and registers it", async () => {
    const { stdout } = await gate([
      GATE_ID, "--consumers", CONSUMER, "--statement", "hBochner: integrability of the offset sSup",
      "--lean-name", "hBochner", "--supersedes", PROSE_LABEL,
    ]);
    expect(stdout).toMatch(/minted/i);

    const g = JSON.parse(await readFile(graphPath(formalizationDir(repoRoot, QID), QID, SPEC), "utf8"));
    const gn = g.nodes.find((n: GraphNode) => n.id === GATE_ID);
    expect(gn.kind).toBe("gate");
    expect(gn.gate.gate_class).toBe("gated");
    expect(g.edges).toContainEqual({ kind: "proof-uses", from: CONSUMER, to: GATE_ID, source: "declared" });

    const plan = JSON.parse(await readFile(planPath(repoRoot, QID, SPEC), "utf8"));
    expect(plan.nodes[GATE_ID]).toMatchObject({ gate: true, gate_class: "gated", lean_name: "hBochner" });
    expect(plan.nodes[CONSUMER].hyps).toContain(GATE_ID);

    // Registering makes the consumer's statement CONDITIONAL → it must be re-reviewed.
    expect(g.nodes.find((n: GraphNode) => n.id === CONSUMER).review.status).toBe("unreviewed");
  });

  // Without --supersedes the prose entry survives alongside the registered one, and the entry
  // carries two disclosures for one debt — the stale one still calling it unregistered.
  it("retires the superseded prose-only disclosure instead of duplicating it", async () => {
    await gate([GATE_ID, "--consumers", CONSUMER, "--statement", "s", "--supersedes", PROSE_LABEL]);
    const st = await loadState(repoRoot, QID, SPEC);
    const gates = (st.added_assumptions ?? []).filter((a) => a.classification === "substrate-gate");
    expect(gates).toHaveLength(1);
    expect(gates[0].label).toBe(`${CONSUMER}:${GATE_ID}`);
    expect(gates.some((a) => a.label === PROSE_LABEL)).toBe(false);
  });

  it("records the minted gate in SUBSTRATE_DEBT.md (the graph `gate-ledger` invariant)", async () => {
    await gate([GATE_ID, "--consumers", CONSUMER, "--statement", "s"]);
    const debt = await readFile(path.join(formalizationDir(repoRoot, QID), "SUBSTRATE_DEBT.md"), "utf8");
    expect(debt).toContain(GATE_ID);
  });

  it("REFUSES to mint without --statement, and says how to supply it", async () => {
    await expect(gate([GATE_ID, "--consumers", CONSUMER])).rejects.toMatchObject({ code: 1 });
    await expect(gate([GATE_ID, "--consumers", CONSUMER])).rejects.toThrow(/--statement/);
  });

  it("REFUSES --supersedes on a label that matches no disclosure (typo guard)", async () => {
    await expect(
      gate([GATE_ID, "--consumers", CONSUMER, "--statement", "s", "--supersedes", "no such label"]),
    ).rejects.toThrow(/matches no existing disclosure/);
  });

  it("REFUSES to mint a gate under a consumer that is not in the graph", async () => {
    await expect(
      gate([GATE_ID, "--consumers", "ghost:node", "--statement", "s"]),
    ).rejects.toThrow(/not in graph|cannot hang/);
  });

  // REGRESSION (seen in a live exp_bipartite discharge): a plan gate node carrying ONLY gate keys
  // (registered by the pipeline scaffolder, not gate.ts's fuller mint) was left as `{}` by
  // `withoutGateKeys` on --ungate — no lean_kind/lean_name/disposition, so it trips the F2 post-sync
  // plan_gate schema on every later run. A node that is nothing but a gate must be DELETED.
  it("DELETES a gate-only plan node on --ungate (no {} husk)", async () => {
    // Seed the husk-producing shape directly: a plan node with only gate keys + a graph gate node.
    const gp = graphPath(formalizationDir(repoRoot, QID), QID, SPEC);
    const g = JSON.parse(await readFile(gp, "utf8"));
    g.nodes.push({ ...node(GATE_ID, "gate"), gate: { gate_class: "gated" }, provenance: "agent-introduced" });
    g.edges.push({ kind: "proof-uses", from: CONSUMER, to: GATE_ID, source: "declared" });
    await writeFile(gp, JSON.stringify(g));
    const pp = planPath(repoRoot, QID, SPEC);
    const plan0 = JSON.parse(await readFile(pp, "utf8"));
    plan0.nodes[GATE_ID] = { gate: true, gate_class: "gated" }; // only gate keys
    plan0.nodes[CONSUMER].hyps = [GATE_ID];
    await writeFile(pp, JSON.stringify(plan0));

    await gate([GATE_ID, "--ungate"]);

    const plan = JSON.parse(await readFile(pp, "utf8"));
    expect(GATE_ID in plan.nodes).toBe(false); // deleted, not {}
    expect(plan.nodes[CONSUMER].hyps).not.toContain(GATE_ID); // consumer survives, un-threaded
  });

  // Complement: a node that pre-existed with a REAL non-gate role keeps its residual on --ungate.
  it("KEEPS a plan node that has a non-gate residual after --ungate", async () => {
    const gp = graphPath(formalizationDir(repoRoot, QID), QID, SPEC);
    const g = JSON.parse(await readFile(gp, "utf8"));
    g.nodes.push({ ...node(GATE_ID, "gate"), gate: { gate_class: "gated" }, provenance: "agent-introduced" });
    await writeFile(gp, JSON.stringify(g));
    const pp = planPath(repoRoot, QID, SPEC);
    const plan0 = JSON.parse(await readFile(pp, "utf8"));
    plan0.nodes[GATE_ID] = { lean_kind: "def", lean_name: "realDef", gate: true, gate_class: "gated" };
    await writeFile(pp, JSON.stringify(plan0));

    await gate([GATE_ID, "--ungate"]);

    const plan = JSON.parse(await readFile(pp, "utf8"));
    expect(plan.nodes[GATE_ID]).toEqual({ lean_kind: "def", lean_name: "realDef" });
  });
});
