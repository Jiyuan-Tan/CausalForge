import { describe, it, expect, afterAll } from "vitest";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge, setProof } from "../../src/graph/mutate.js";
import { runFiller, renderFillerContext } from "../../src/formalization/proof_filler.js";

// The filler dispatches a WRITE-CAPABLE agent, so it must never run on a degraded prompt: the
// base prompt carries the no-axiom / disclosure / frozen-statement contract. Point every test at
// the real prompt file rather than letting a missing one silently become "".
const realPromptPath = join(process.cwd(), "src/formalization/prompts/F4/proof_filler.txt");

function fixture() {
  let g = createEmptyGraph("q", "v1");
  g = addNode(g, { id: "setup", kind: "setup", provenance: "from-note", nl_statement: "PO env", tex_anchor: "" });
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "the rate holds", tex_anchor: "L1" });
  g = { ...g, nodes: g.nodes.map((n) => (n.id === "t1" ? { ...n, lean: { decl_name: "t1_thm", file: "T1.lean" } } : n)) };
  g = setProof(g, "t1", "sorry", 1);
  g = addEdge(g, { kind: "setup-of", from: "setup", to: "t1", source: "declared" });
  return g;
}

function fixtureWithObjAlias() {
  let g = createEmptyGraph("q", "v1");
  g = addNode(g, { id: "setup", kind: "setup", provenance: "from-note", nl_statement: "PO env", tex_anchor: "" });
  g = addNode(g, { id: "thm:main", kind: "theorem", provenance: "from-note", nl_statement: "the rate holds", tex_anchor: "L1" });
  g = { ...g, nodes: g.nodes.map((n) => (n.id === "thm:main" ? { ...n, obj_id: "T-1", lean: { decl_name: "t1_thm", file: "T1.lean" } } : n)) };
  g = setProof(g, "thm:main", "sorry", 1);
  g = addEdge(g, { kind: "setup-of", from: "setup", to: "thm:main", source: "declared" });
  return g;
}

const codexStub = (out: object) => ({
  runCodex: async () => ({ stdout: JSON.stringify(out), stderr: "" }),
});

// A real writable dir: the filler now dispatches through the framework boundary
// (dispatchAgent), which appends a dispatch/dispatch-complete pair to
// <repoRoot>/.../pipeline.jsonl before/after each call — an unwritable fake root
// like "/repo" trips EACCES on that mkdir.
const fillerRepoRoot = mkdtempSync(join(tmpdir(), "proof-filler-ctx-"));
afterAll(() => rmSync(fillerRepoRoot, { recursive: true, force: true }));
const ctx = { repoRoot: fillerRepoRoot, qid: "q", specialization: "v1" };

describe("renderFillerContext", () => {
  it("lists open nodes + their frozen statements", () => {
    const s = renderFillerContext(fixture());
    expect(s).toContain("t1");
    expect(s).toContain("the rate holds");
  });

  it("deduplicates a dependency carried by both statement-uses and proof-uses", () => {
    let g = fixture();
    g = addNode(g, {
      id: "a1",
      kind: "assumption",
      provenance: "from-note",
      nl_statement: "shared interface",
      tex_anchor: "",
    });
    g = addEdge(g, { kind: "statement-uses", from: "t1", to: "a1", source: "extracted" });
    g = addEdge(g, { kind: "proof-uses", from: "t1", to: "a1", source: "declared" });

    const line = renderFillerContext(g).split("\n").find((s) => s.startsWith("- t1"))!;
    expect(line).toContain("uses: a1");
    expect(line.match(/\ba1\b/g)).toHaveLength(1);
  });
});

describe("runFiller", () => {
  it("uses medium reasoning effort for F3 proof filling", async () => {
    let received: { reasoningEffort?: string } | undefined;
    await runFiller({
      ctx,
      promptPath: realPromptPath,
      leanDir: "/repo/lean",
      graph: fixture(),
      deps: {
        runCodex: async (input) => {
          received = input;
          return { stdout: JSON.stringify({ summary: "closed 1 sorry" }), stderr: "" };
        },
      },
    });
    expect(received?.reasoningEffort).toBe("medium");
  });

  it("records an added assumption as a node + proof-uses edge and flips the parent unreviewed", async () => {
    const r = await runFiller({
      ctx,
      promptPath: realPromptPath,
      leanDir: "/repo/lean",
      graph: fixture(),
      deps: codexStub({
        worked_on: ["thm:main"],
        added_assumptions: [
          { id: "a9", statement: "the outcome is bounded", classification: "regularity-bookkeeping", attached_to: "t1" },
        ],
        escalate: null,
        summary: "added boundedness; closed 1 sorry",
      }),
    });
    const a9 = r.graph.nodes.find((n) => n.id === "a9")!;
    expect(a9.kind).toBe("assumption");
    expect(a9.provenance).toBe("agent-introduced");
    expect(r.graph.edges).toContainEqual({ kind: "proof-uses", from: "t1", to: "a9", source: "declared" });
    expect(r.graph.nodes.find((n) => n.id === "t1")!.review.status).toBe("unreviewed");
    expect(r.escalate).toBeNull();
  });

  it("attaches filler assumptions to a parent's obj_id alias", async () => {
    const r = await runFiller({
      ctx,
      promptPath: realPromptPath,
      leanDir: "/repo/lean",
      graph: fixtureWithObjAlias(),
      deps: codexStub({
        worked_on: ["t1"],
        added_assumptions: [
          { id: "a10", statement: "the law is tight", classification: "mathematical-regularity", attached_to: "T-1" },
        ],
        escalate: null,
        summary: "added alias-attached assumption",
      }),
    });
    expect(r.graph.nodes.some((n) => n.id === "a10")).toBe(true);
    expect(r.graph.edges).toContainEqual({ kind: "proof-uses", from: "thm:main", to: "a10", source: "declared" });
    expect(r.graph.nodes.find((n) => n.id === "thm:main")!.review.status).toBe("unreviewed");
  });

  // A degraded base prompt strips the no-axiom / disclosure / frozen-statement contract while
  // leaving the agent's write access intact, so the filler must refuse to dispatch at all.
  it("refuses to dispatch when the base prompt is missing", async () => {
    let dispatched = false;
    await expect(
      runFiller({
        ctx,
        promptPath: join(tmpdir(), "causalsmith-no-such-proof-filler-prompt.txt"),
        leanDir: "/repo/lean",
        graph: fixture(),
        deps: { runCodex: async () => { dispatched = true; return { stdout: "{}", stderr: "" }; } },
      }),
    ).rejects.toThrow(/proof-filler prompt missing/);
    expect(dispatched).toBe(false);
  });

  it("refuses to dispatch when the base prompt is blank", async () => {
    const dir = await mkdtemp(join(tmpdir(), "filler-blank-prompt-"));
    const blank = join(dir, "proof_filler.txt");
    await writeFile(blank, "   \n\n");
    let dispatched = false;
    try {
      await expect(
        runFiller({
          ctx,
          promptPath: blank,
          leanDir: "/repo/lean",
          graph: fixture(),
          deps: { runCodex: async () => { dispatched = true; return { stdout: "{}", stderr: "" }; } },
        }),
      ).rejects.toThrow(/proof-filler prompt is empty/);
      expect(dispatched).toBe(false);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  // The loop has no stage-level catch, so a throw here would abort the whole run on one flaky
  // model reply. Mirror the reviewer's parse boundary: escalate `unparsable-output` instead.
  it("escalates (not throws) when the filler output has no parseable JSON", async () => {
    const r = await runFiller({
      ctx,
      promptPath: realPromptPath,
      leanDir: "/repo/lean",
      graph: fixture(),
      deps: { runCodex: async () => ({ stdout: "I could not finish; no JSON here.", stderr: "" }) },
    });
    expect(r.escalate?.kind).toBe("unparsable-output");
    expect(r.graph).toEqual(fixture());
  });

  // An assumption attached to an unknown parent cannot land on the graph; it must be dropped
  // LOUDLY (the Lean already carries the hypothesis — a silent drop loses the disclosure).
  it("warns when an added assumption's parent cannot be resolved, and does not mint the node", async () => {
    const warns: string[] = [];
    const orig = console.warn;
    console.warn = (...a: unknown[]) => { warns.push(a.map(String).join(" ")); };
    try {
      const r = await runFiller({
        ctx,
        promptPath: realPromptPath,
        leanDir: "/repo/lean",
        graph: fixture(),
        deps: codexStub({
          added_assumptions: [
            { id: "a11", statement: "smuggled", classification: "substrate-gate", attached_to: "no-such-node" },
          ],
          escalate: null,
          summary: "attached to ghost",
        }),
      });
      expect(r.graph.nodes.some((n) => n.id === "a11")).toBe(false);
      expect(r.escalate).toBeNull();
      expect(warns.some((w) => w.includes("a11") && w.includes("no-such-node"))).toBe(true);
    } finally {
      console.warn = orig;
    }
  });

  it("surfaces an escalation", async () => {
    const r = await runFiller({
      ctx,
      promptPath: realPromptPath,
      leanDir: "/repo/lean",
      graph: fixture(),
      deps: codexStub({ worked_on: [], added_assumptions: [], escalate: { kind: "needs-substrate", reason: "needs a concentration bound", node: "t1" }, summary: "stuck" }),
    });
    expect(r.escalate).toEqual({ kind: "needs-substrate", reason: "needs a concentration bound", node: "t1" });
  });
});
