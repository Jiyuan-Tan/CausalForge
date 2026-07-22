#!/usr/bin/env -S npx tsx
/**
 * Orchestrator-only: register a graph node as a SUBSTRATE-GATE (accepted, disclosed debt)
 * in ONE atomic operation across the plan, graph, and state — so the F2 scaffolder keeps
 * it as a `_of_gate` hypothesis (never re-emits it as an inline `sorry`), the F2.5/F4
 * reviewer ASSUMES it (never re-escalates `needs-substrate`), and F5 banks it as disclosed
 * substrate-debt.
 *
 * WHY THIS EXISTS: hand-adding a gate hypothesis to a `.lean` theorem does NOT survive an
 * F2 re-scaffold — the scaffolder rebuilds the statement from `plan.json`, drops the
 * un-registered hypothesis, and the residual becomes an inline `sorry` the filler then
 * escalates `build-substrate` on. Gate registration must live in the PLAN (+ graph + state),
 * which is exactly what this command does. Two consumers honor that registration so the gate
 * is DURABLE with no hand-editing: (a) the F2 scaffolder (`gatedHypsBlockFromPlan` in stage2.ts)
 * reads the `gated` plan nodes and emits each as an EXPLICIT `_of_gate` HYPOTHESIS on every
 * consumer that threads it (never an in-proof `sorry`); (b) the F2.5 + F4 reviewers
 * (`proof_reviewer.ts`) EXEMPT a consumer's gated hypothesis from the added-premise / drift /
 * content-gate check (it is disclosed debt, not laundering). So a gate registered here survives
 * every re-scaffold AND passes review as a sorry-free CONDITIONAL, without any manual `.lean` edit.
 *
 * WHAT IT DOES (idempotent):
 *   1. plan.json: ensure the node exists with `gate:true`, `gate_class`, `lean_kind:"assumption"`,
 *      and add `<node_id>` to every consumer's `hyps` (so F2 threads it as a hypothesis).
 *   2. graph.json: set the node `kind:"gate"` + `gate:{gate_class, source?}`, add a `proof-uses`
 *      edge consumer→node, and flip each consumer back to `unreviewed` (so F2.5 re-checks the
 *      now-conditional statement).
 *   3. state.json: append an `added_assumptions` disclosure (classification `substrate-gate`).
 *   4. SUBSTRATE_DEBT.md: append a human-readable debt line.
 *
 * gate_class:
 *   - "gated"  (default): assumed to parallelize fill; DISCHARGE before banking when feasible,
 *      else it stays honest substrate-debt. Use for our own hard fact (delta-method core, etc.).
 *   - "cited": a borrowed/classical result; requires `--source` for F2.5 source-matching.
 *
 * Usage:
 *   npx tsx tools/bin/gate.ts <qid> <spec> <node_id> --consumers <id1,id2,...> [--class gated|cited] \
 *       [--lean-name <Name>] [--source "<cite>"] [--reason "<why it's genuine debt>"]
 *   npx tsx tools/bin/gate.ts <qid> <spec> <node_id> --show
 *
 * DISCHARGE / de-register (the reverse operation — use once the gate is PROVEN, or to undo a
 * mistaken registration). `--ungate` / `--discharge` / `--unset` are synonyms and do the FULL
 * reverse in one atomic operation: drop `gate` from the plan + graph node, un-thread it from
 * every consumer's `hyps`, remove the `proof-uses` gate edges, reopen the consumers for
 * re-review (so F2.5/F4 re-verify each is now honestly UNCONDITIONAL), and delete the
 * disclosure from `state.added_assumptions` + the `gate.ts`-appended `SUBSTRATE_DEBT.md`
 * bullet. Consumers are auto-detected from the graph/plan, so `--consumers` is optional here.
 * Pass `--lean-name <Name>` to also clear an F5-derived disclosure keyed by the Lean type name.
 *   npx tsx tools/bin/gate.ts <qid> <spec> <node_id> --discharge [--lean-name <Name>]
 */
import { existsSync, readFileSync, writeFileSync, appendFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import { loadState, saveState } from "../src/state.js";
import { loadGraph, saveGraph, graphPath } from "../src/graph/store.js";
import { addAssumption } from "../src/graph/mutate.js";
import { planPath } from "../src/paths.js";
import {
  deriveGateConsumers,
  auditSubstrateGates,
  gateIdentityStrings,
  isGateDisclosure,
  isGateDebtBullet,
  withoutGateKeys,
} from "../src/formalization/gate_ops.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";

function flag(args: string[], name: string): string | undefined {
  const i = args.indexOf(name);
  return i >= 0 && i + 1 < args.length ? args[i + 1] : undefined;
}
function has(args: string[], name: string): boolean {
  return args.includes(name);
}
function formalizationDir(repoRoot: string, qid: string): string {
  const kind = /^(study|_)/.test(qid) ? "study" : "research";
  return kind === "research"
    ? path.join(repoRoot, "doc", "research", "active", qid)
    : path.join(repoRoot, "doc", "study", "runs", qid);
}

async function main() {
  const args = process.argv.slice(2);
  const [qid, spec, nodeId] = args;
  const auditMode = has(args, "--audit");
  if (!qid || !spec || (!nodeId && !auditMode)) {
    console.error(
      "usage: gate.ts <qid> <spec> <node_id> --consumers <id1,id2> [--class gated|cited] [--source ..] [--reason ..] [--show]\n" +
        "         [--statement \"<premise>\"]   # MINT the node when it does not exist yet (prose-only debt)\n" +
        "         [--supersedes \"<label>\"]    # retire the prose-only disclosure this registration replaces\n" +
        "       gate.ts <qid> <spec> <node_id> --discharge [--lean-name <Name>]   # reverse: --discharge | --ungate | --unset\n" +
        "       gate.ts <qid> <spec> --audit   # list disclosed substrate-gates that are NOT registered (what blocks banking 'accepted')",
    );
    process.exit(2);
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const fdir = formalizationDir(repoRoot, qid);
  const gpath = graphPath(fdir, qid, spec);
  const ppath = planPath(repoRoot, qid, spec);

  // `--audit`: the pre-flight for banking. `bankEntry` refuses tier `accepted` while any disclosed
  // `substrate-gate` lacks a registered node; this surfaces the same findings on demand, so the
  // orchestrator learns about them BEFORE the bank refuses rather than after.
  if (auditMode) {
    // A BANKED entry has no working dir, and `loadGraph` would die on a raw ENOENT that reads
    // like a tooling bug. Say what happened and how to inspect it instead.
    if (!existsSync(gpath)) {
      console.error(
        `gate --audit: no working dir for ${qid}/${spec} (looked for ${path.relative(repoRoot, gpath)}).\n` +
          `If the entry is BANKED, --audit cannot read it in place. Reopen it first:\n` +
          `  npx tsx tools/bin/causalsmith.ts research --reopen ${qid} ${spec}\n` +
          `(bankEntry re-runs this same audit on any re-bank at tier 'accepted', so a banked entry\n` +
          ` cannot be re-banked while a disclosed substrate-gate is unregistered.)`,
      );
      process.exit(2);
    }
    const g = await loadGraph(gpath);
    const p = existsSync(ppath) ? JSON.parse(readFileSync(ppath, "utf8")) : null;
    const st = await loadState(repoRoot, qid, spec);
    const planNodes = Object.entries((p?.nodes ?? {}) as Record<string, Record<string, unknown>>).map(
      ([id, n]) => ({ id, ...n }),
    ) as Parameters<typeof auditSubstrateGates>[0]["planNodes"];
    const findings = auditSubstrateGates({
      addedAssumptions: st.added_assumptions ?? [],
      planNodes,
      graphNodes: g.nodes as Parameters<typeof auditSubstrateGates>[0]["graphNodes"],
    });
    if (findings.length === 0) {
      console.log(`gate --audit: ${qid}/${spec} clean — every disclosed substrate-gate is registered.`);
      return;
    }
    console.error(`gate --audit: ${findings.length} disclosed substrate-gate(s) NOT registered (blocks banking 'accepted'):`);
    for (const f of findings) console.error(`  - ${f.label}: ${f.reason}`);
    process.exit(1);
  }
  const gateClass = (flag(args, "--class") as "gated" | "cited" | undefined) ?? "gated";
  const source = flag(args, "--source");
  const reason = flag(args, "--reason") ?? "";
  const leanName = flag(args, "--lean-name");
  /** Premise text, required only when MINTING a gate node that does not exist yet. */
  const statement = flag(args, "--statement");
  /** Exact label of a prose-only disclosure this registration replaces (retired, not duplicated). */
  const supersedes = flag(args, "--supersedes");
  // `--discharge` (aka `--ungate`, `--unset`) is the reverse of registration.
  const ungate = has(args, "--unset") || has(args, "--ungate") || has(args, "--discharge");
  let consumers = (flag(args, "--consumers") ?? "").split(",").map((s) => s.trim()).filter(Boolean);

  let graph = await loadGraph(gpath);
  const plan = existsSync(ppath) ? JSON.parse(readFileSync(ppath, "utf8")) : null;

  // MINT. A debt disclosed only in prose (`state.added_assumptions` with no plan/graph node —
  // what `--audit` reports as "prose-only and unenforceable") has no node to register, so
  // registration was impossible: the only path out of the defect was blocked. Mint the node
  // through the graph mutate API (never a hand-edit), hanging it off the first consumer; the
  // gate step below flips `kind: "assumption"` → `"gate"` and threads the rest.
  if (!graph.nodes.some((n) => n.id === nodeId)) {
    if (ungate) { console.error(`gate: node ${nodeId} not in graph ${gpath} — nothing to discharge.`); process.exit(1); }
    if (!statement || consumers.length === 0) {
      console.error(
        `gate: node ${nodeId} not in graph ${path.relative(repoRoot, gpath)}.\n` +
          `To MINT it as a new substrate-gate, supply both the premise text and who assumes it:\n` +
          `  npx tsx tools/bin/gate.ts ${qid} ${spec} ${nodeId} \\\n` +
          `    --consumers <id1,id2> --statement "<the premise, as it stands in Lean>" [--lean-name <Name>]`,
      );
      process.exit(1);
    }
    const parent = consumers[0];
    if (!graph.nodes.some((n) => n.id === parent)) {
      console.error(`gate: consumer ${parent} not in graph — cannot hang a minted gate off a missing node.`);
      process.exit(1);
    }
    graph = addAssumption(graph, {
      node: parent, id: nodeId, statement, tier: 2,
      classification: "substrate-gate", anchor: parent, provenance: "agent-introduced",
    });
    console.log(`gate: minted ${nodeId} (was prose-only debt) under ${parent}.`);
  }

  const gnode = graph.nodes.find((n) => n.id === nodeId)!;

  // Discharge: auto-detect the consumers threading this gate (graph `proof-uses` ∪ plan `hyps`),
  // so the caller need not re-supply the exact `--consumers` used at registration.
  if (ungate && consumers.length === 0) {
    consumers = deriveGateConsumers(graph.edges, plan?.nodes, nodeId);
  }

  if (has(args, "--show")) {
    console.log(JSON.stringify({ id: nodeId, kind: gnode.kind, gate: (gnode as { gate?: unknown }).gate,
      plan: plan?.nodes?.[nodeId] ?? null }, null, 2));
    return;
  }

  // ---- 1. plan.json: register (gate) or clear (discharge) + (un)thread consumers' hyps ----
  if (plan?.nodes) {
    const pn = plan.nodes[nodeId] ?? {};
    if (ungate) {
      const stripped = withoutGateKeys(pn as Record<string, unknown>);
      // A gate-only plan node (nothing left once the gate keys go) must be DELETED, not left as
      // `{}` — an empty entry has no `lean_kind`/`lean_name`/`disposition` and trips the F2
      // post-sync `plan_gate` schema check on every subsequent run. Only a node that carried a
      // real non-gate role keeps its residual.
      if (Object.keys(stripped).length === 0) delete plan.nodes[nodeId];
      else plan.nodes[nodeId] = stripped;
    } else {
      plan.nodes[nodeId] = {
        ...pn,
        lean_kind: "assumption",
        lean_name: leanName ?? pn.lean_name ?? nodeId,
        gate: true,
        gate_class: gateClass,
        ...(source ? { source } : {}),
        disposition: pn.disposition ?? "define-local",
      };
    }
    for (const c of consumers) {
      const cn = plan.nodes[c];
      if (!cn) continue;
      cn.hyps = Array.isArray(cn.hyps) ? cn.hyps : [];
      if (ungate) cn.hyps = cn.hyps.filter((h: string) => h !== nodeId);
      else if (!cn.hyps.includes(nodeId)) cn.hyps.push(nodeId);
    }
    writeFileSync(ppath, JSON.stringify(plan, null, 2));
  }

  // ---- 2. graph.json: mark gate + proof-uses edges + reopen consumers for re-review ------
  let g = graph;
  g = {
    ...g,
    nodes: g.nodes.map((n) => {
      if (n.id === nodeId) {
        return ungate
          ? { ...n, kind: "definition" as const, gate: undefined }
          : { ...n, kind: "gate" as const, gate: { gate_class: gateClass, ...(source ? { source } : {}) } };
      }
      // Reopen every consumer for re-review in BOTH directions: registering makes its
      // statement conditional; discharging makes it unconditional — either way F2.5/F4 must
      // re-verify it rather than trust the stale verdict.
      if (consumers.includes(n.id)) {
        return { ...n, review: { ...n.review, status: "unreviewed" as const } };
      }
      return n;
    }),
  };
  const edgeExists = (from: string, to: string) =>
    g.edges.some((e) => e.kind === "proof-uses" && e.from === from && e.to === to);
  for (const c of consumers) {
    if (ungate) {
      g = { ...g, edges: g.edges.filter((e) => !(e.kind === "proof-uses" && e.from === c && e.to === nodeId)) };
    } else if (g.nodes.some((n) => n.id === c) && !edgeExists(c, nodeId)) {
      g = { ...g, edges: [...g.edges, { kind: "proof-uses" as const, from: c, to: nodeId, source: "declared" as const }] };
    }
  }
  await saveGraph(gpath, g);

  // ---- 3. state.json: disclose (register) or remove (discharge) the added assumption -----
  const state = await loadState(repoRoot, qid, spec);
  // Identity strings: node id + Lean realization name(s). F5 keys its derived disclosure by
  // the Lean TYPE name while gate.ts keys its own by the node id, so discharge matches both.
  //
  // Three sources, so `--lean-name` is a fallback rather than a requirement: the plan node's
  // `lean_name` (written at registration), the GRAPH node's `lean.decl_name` (present even for a
  // never-registered node, whose plan entry does not exist — the legacy case that stranded an F5
  // disclosure after discharge), and finally the explicit flag.
  const declName = (gnode as { lean?: { decl_name?: string } }).lean?.decl_name;
  const declBase = declName?.split(".").pop();
  const ids = gateIdentityStrings(
    nodeId,
    plan?.nodes?.[nodeId]?.lean_name as string | undefined,
    declBase,
    leanName,
  );
  const label = `${consumers[0] ?? nodeId}:${nodeId}`;
  let aa = state.added_assumptions ?? [];
  const disclosuresBefore = aa.length;
  if (ungate) {
    aa = aa.filter((a) => !isGateDisclosure(a, ids));
  } else {
    // Retire the prose-only disclosure this registration supersedes. Its label predates the gate
    // node, so it matches neither `label` nor `isGateDisclosure(ids)` — without this the entry ends
    // up with TWO disclosures for one debt, and the stale one keeps describing it as unregistered.
    if (supersedes) {
      if (!aa.some((a) => a.label === supersedes)) {
        console.error(`gate: --supersedes "${supersedes}" matches no existing disclosure label.`);
        process.exit(1);
      }
      aa = aa.filter((a) => a.label !== supersedes);
    }
    aa = aa.filter((a) => a.label !== label);
    aa.push({
      label,
      statement: `${nodeId} — substrate-gate (${gateClass})${reason ? `: ${reason}` : ""}`,
      classification: "substrate-gate",
      anchor: consumers[0] ?? nodeId,
      source: reason || `registered via bin/gate.ts as ${gateClass} substrate-gate; threaded into ${consumers.join(", ")}`,
    });
  }
  const disclosuresRemoved = disclosuresBefore - aa.length;
  state.added_assumptions = aa;
  await saveState(repoRoot, qid, spec, state);

  // ---- 4. SUBSTRATE_DEBT.md: append (register) or remove our own bullet (discharge) -------
  const debtPath = path.join(fdir, "SUBSTRATE_DEBT.md");
  let debtRemoved = 0;
  if (ungate) {
    if (existsSync(debtPath)) {
      const lines = readFileSync(debtPath, "utf8").split("\n");
      const kept = lines.filter((l) => !isGateDebtBullet(l, ids));
      debtRemoved = lines.length - kept.length;
      if (debtRemoved > 0) writeFileSync(debtPath, kept.join("\n"));
    }
  } else {
    if (!existsSync(debtPath)) writeFileSync(debtPath, "# Substrate debt (disclosed gates)\n\n");
    if (!readFileSync(debtPath, "utf8").includes(nodeId)) {
      appendFileSync(debtPath, `- **${nodeId}** (${gateClass}) — gated substrate-debt on ${consumers.join(", ")}${reason ? `. ${reason}` : ""}\n`);
    }
  }

  console.log(ungate
    ? `gate: DISCHARGED ${nodeId} — cleared gate on plan+graph; un-threaded from [${consumers.join(", ") || "(none detected)"}] + reopened for re-review; removed ${disclosuresRemoved} disclosure(s), ${debtRemoved} debt line(s).`
    : `gate: registered ${nodeId} as ${gateClass} substrate-gate; threaded into hyps of ${consumers.join(", ") || "(no consumers given!)"}; disclosed in state + SUBSTRATE_DEBT.md`);
}

main().catch((e) => { console.error(e instanceof Error ? e.message : String(e)); process.exit(1); });
