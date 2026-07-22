import { createEmptyGraph, graphPath, loadGraph, saveGraph } from "./store.js";
import { addAssumption, addNode, setNodeReview } from "./mutate.js";
import { extractFromLean } from "./extractor.js";
import { statementHash } from "./hash.js";
import { validate } from "./validator.js";
import { dirtyFrontier } from "./diff.js";
import { toDot, toMarkdown } from "./project.js";
import type { AssumptionClass, NodeKind, Provenance } from "./types.js";

function flag(args: string[], name: string): string | undefined {
  const i = args.indexOf(`--${name}`);
  return i >= 0 ? args[i + 1] : undefined;
}
function need(args: string[], name: string): string {
  const v = flag(args, name);
  if (v === undefined) throw new Error(`missing --${name}`);
  return v;
}
function has(args: string[], name: string): boolean {
  return args.includes(`--${name}`);
}
function parseTier(raw: string): 1 | 2 {
  if (raw === "1" || raw === "2") return Number(raw) as 1 | 2;
  throw new Error(`invalid --tier ${raw}; expected 1 or 2`); // why: avoid silently demoting bad tiers to 2.
}

/** The verb is the first bare token NOT consumed as a flag value. */
function findVerb(args: string[]): string | undefined {
  for (let i = 0; i < args.length; i++) {
    if (!args[i].startsWith("--") && (i === 0 || !args[i - 1].startsWith("--"))) return args[i];
  }
  return undefined;
}

export async function runCli(args: string[]): Promise<number> {
  const verb = findVerb(args);
  try {
    const dir = need(args, "dir");
    const qid = need(args, "qid");
    const spec = need(args, "spec");
    const p = graphPath(dir, qid, spec);

    switch (verb) {
      case "init": {
        await saveGraph(p, createEmptyGraph(qid, spec));
        return 0;
      }
      case "add-node": {
        let g = await loadGraph(p);
        g = addNode(g, {
          id: need(args, "id"),
          kind: need(args, "kind") as NodeKind,
          provenance: need(args, "provenance") as Provenance,
          nl_statement: need(args, "nl"),
          tex_anchor: flag(args, "anchor") ?? "",
        });
        await saveGraph(p, g);
        return 0;
      }
      case "add-assumption": {
        let g = await loadGraph(p);
        g = addAssumption(g, {
          node: need(args, "node"),
          id: need(args, "id"),
          statement: need(args, "statement"),
          tier: parseTier(need(args, "tier")),
          classification: need(args, "classification") as AssumptionClass,
          anchor: flag(args, "anchor") ?? "",
          provenance: need(args, "provenance") as Provenance,
        });
        await saveGraph(p, g);
        return 0;
      }
      case "extract": {
        const g = await loadGraph(p);
        const { graph, unlinked } = await extractFromLean(g, need(args, "lean-dir"));
        await saveGraph(p, graph);
        if (unlinked.length) {
          process.stdout.write(JSON.stringify({ unlinked }, null, 2) + "\n");
          return 2;
        }
        return 0;
      }
      case "validate": {
        const g = await loadGraph(p);
        const r = validate(g);
        if (has(args, "json")) process.stdout.write(JSON.stringify(r, null, 2) + "\n");
        else
          for (const f of r.findings)
            process.stdout.write(`[${f.severity}] ${f.invariant}${f.node ? ` (${f.node})` : ""}: ${f.message}\n`);
        return r.ok ? 0 : 1;
      }
      case "diff": {
        const g = await loadGraph(p);
        const { hashes } = await extractFromLean(g, need(args, "lean-dir"));
        process.stdout.write(JSON.stringify({ dirty: dirtyFrontier(g, hashes) }, null, 2) + "\n");
        return 0;
      }
      case "accept-review": {
        // Persist an orchestrator ACCEPT-AS-IS adjudication of a reviewer flag.
        // Without this, an over-strict F2.5 verdict adjudicated at a halt had nowhere
        // durable to live: graph.json kept `review.status: drift`, so the node re-entered
        // the dirty frontier on every later resume and was re-flagged indefinitely
        // (observed: one node re-reviewed across 3+ resumes after its accept-as-is
        // decision was recorded only in the decision log). Records status `matched` at
        // the node's CURRENT Lean statement hash — any later real statement change
        // still re-dirties it.
        const id = need(args, "id");
        let g = await loadGraph(p);
        const node = g.nodes.find((n) => n.id === id);
        if (!node) throw new Error(`accept-review: unknown node ${id}`);
        const { hashes } = await extractFromLean(g, need(args, "lean-dir"));
        const hash = hashes[id] ?? statementHash(node.nl.statement);
        g = setNodeReview(g, id, "matched", hash, flag(args, "note") ?? "orchestrator accept-as-is");
        await saveGraph(p, g);
        process.stdout.write(JSON.stringify({ accepted: id, passed_hash: hash }) + "\n");
        return 0;
      }
      case "show": {
        const g = await loadGraph(p);
        process.stdout.write((has(args, "dot") ? toDot(g) : toMarkdown(g)) + "\n");
        return 0;
      }
      default:
        process.stderr.write(`unknown verb: ${verb ?? "(none)"}\n`);
        return 64;
    }
  } catch (err) {
    process.stderr.write(`graph: ${(err as Error).message}\n`);
    return 70;
  }
}
