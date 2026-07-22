import { describe, it, expect } from "vitest";
import { FormalLayerSource, blocksToTex, texEnvFor, hashBody, blocksFromGraph, normalizeCitedScopeFootnotes, paperEnvMismatches, type FormalBlock } from "../src/presentation/formal_layer.js";
import { parseAnchoredEnvs } from "../src/presentation/tex_anchors.js";
import type { FormalizationGraph } from "../src/graph/types.js";

const gnode = (
  id: string, obj_id: string | null, kind: FormalizationGraph["nodes"][number]["kind"],
  decl: string | null,
): FormalizationGraph["nodes"][number] => ({
  id, obj_id: obj_id ?? undefined, kind, provenance: "from-note",
  nl: { statement: id, tex_anchor: "", frozen: true },
  lean: { decl_name: decl, file: decl ? "T.lean" : null },
  review: { status: "matched", passed_hash: null },
  proof: { state: "complete", sorry_count: 0 },
});

const graphFixture: FormalizationGraph = {
  qid: "q", specialization: "s",
  nodes: [gnode("thm:m", "T-1", "theorem", "mainThm"), gnode("ass:x", "A-1", "assumption", "AssX")],
  edges: [{ kind: "statement-uses", from: "thm:m", to: "ass:x", source: "declared" }],
};

const block: FormalBlock = {
  obj_id: "thm:m",
  alias: "T-1",
  kind: "theorem",
  env: "theoremv",
  title: "Main",
  body: "Under Assumption~\\ref{obj:ass:x}, the bound holds.",
  ref_set: ["ass:x"],
  lean: { decl: "mainThm", file: "T.lean" },
  status: "matched",
  provenance: "from-note",
  cited_dependencies: [],
  body_hash: "deadbeef",
};

describe("formal layer source", () => {
  it("validates the schema and round-trips a block", () => {
    const parsed = FormalLayerSource.parse({ commit: null, blocks: [block] });
    expect(parsed.blocks[0].obj_id).toBe("thm:m");
    expect(parsed.blocks[0].lean?.decl).toBe("mainThm");
  });

  it("blocksToTex emits the env keyed by obj_id (node id) with title + body", () => {
    const tex = blocksToTex([block]);
    expect(tex).toContain("\\begin{theoremv}{thm:m}[Main]");
    expect(tex).toContain("Under Assumption~\\ref{obj:ass:x}");
    expect(tex).toContain("\\end{theoremv}");
  });

  it("blocksToTex skips a decl-less setup block (env null)", () => {
    const setup: FormalBlock = { ...block, obj_id: "S-1", kind: "setup", env: null, title: null, lean: null };
    expect(blocksToTex([setup])).toBe("");
    expect(texEnvFor(setup)).toBe("");
  });

  it("hashBody is whitespace-insensitive (reflow is not a change)", () => {
    expect(hashBody("a   b\n c")).toBe(hashBody("a b c"));
    expect(hashBody("a b c")).toHaveLength(64);
  });

  it("blocksFromGraph builds a block per rendered node, obj_id = node id, lean/status/ref_set from graph", () => {
    const blocks = blocksFromGraph(graphFixture, new Map([["thm:m", "BODY"]]), new Map([["thm:m", "Main"]]));
    const b = blocks.find((x) => x.obj_id === "thm:m")!;
    expect(b.alias).toBe("T-1");
    expect(b.env).toBe("theoremv");
    expect(b.lean).toEqual({ decl: "mainThm", file: "T.lean" });
    expect(b.ref_set).toContain("ass:x"); // statement-uses target, by node id
    expect(b.body).toBe("BODY");
    expect(b.body_hash).toHaveLength(64);
    // the assumption node also renders (frozen + env-kind), with an empty body when not supplied
    expect(blocks.find((x) => x.obj_id === "ass:x")?.body).toBe("");
  });

  it("blocksFromGraph honors env_overrides but rejects a remarkv demotion of a load-bearing object", () => {
    // ass:x is depended on by the proved theorem thm:m → it is load-bearing.
    const free = gnode("oeq:open", "Q-1", "definition", null); // nothing depends on it
    const g: FormalizationGraph = { ...graphFixture, nodes: [...graphFixture.nodes, free] };
    const bodies = new Map([["thm:m", "B"], ["ass:x", "B"], ["oeq:open", "B"]]);
    const dropped: string[] = [];
    const blocks = blocksFromGraph(g, bodies, new Map(), { "ass:x": "definitionv", "oeq:open": "remarkv" }, (m) => dropped.push(m));
    expect(blocks.find((x) => x.obj_id === "ass:x")!.env).toBe("definitionv"); // swap honored
    expect(blocks.find((x) => x.obj_id === "oeq:open")!.env).toBe("remarkv"); // non-load-bearing → remark
    // a remarkv demotion of the load-bearing ass:x is refused, with a logged reason
    const blocked = blocksFromGraph(g, bodies, new Map(), { "ass:x": "remarkv" }, (m) => dropped.push(m));
    expect(blocked.find((x) => x.obj_id === "ass:x")!.env).toBe("assumptionv"); // override ignored
    expect(dropped.some((m) => /load-bearing/.test(m))).toBe(true);
  });

  it("the derived .tex round-trips: parseAnchoredEnvs recovers every block's obj_id + body", () => {
    // The migration safety net — P2/P4 parse the derived .tex during the transition, so the env
    // set and bodies it recovers must equal the source blocks exactly (label = node id obj_id).
    const blocks: FormalBlock[] = [
      { ...block, obj_id: "thm:m", env: "theoremv", title: "Main", body: "Body of T.\n\\[ x \\le y \\]" },
      { ...block, obj_id: "ass:x", alias: "A-1", kind: "assumption", env: "assumptionv", title: "X", body: "0 < e < 1." },
    ];
    const parsed = parseAnchoredEnvs(blocksToTex(blocks));
    expect(parsed.map((e) => e.obj_id)).toEqual(["thm:m", "ass:x"]);
    for (const b of blocks) {
      const e = parsed.find((p) => p.obj_id === b.obj_id)!;
      expect(e.body.trim()).toBe(b.body.trim());
      expect(e.title).toBe(b.title);
    }
  });

  it("paperEnvMismatches: clean assembly passes; a missing or drifted env is flagged", () => {
    const blocks: FormalBlock[] = [{ ...block, obj_id: "thm:m", env: "theoremv", title: "M", body: "X holds." }];
    const paper = `\\section{Main}\nText.\n${blocksToTex(blocks)}\nMore text.`;
    expect(paperEnvMismatches(paper, blocks)).toEqual([]);
    expect(paperEnvMismatches("no envs here", blocks)).toEqual(["thm:m: env missing from paper.tex"]);
    const drifted = paper.replace("X holds", "X fails");
    expect(paperEnvMismatches(drifted, blocks)).toEqual(["thm:m: body differs from formal_layer.json"]);
    // a setup (env null) block is not expected in the paper as an env
    expect(paperEnvMismatches("", [{ ...block, env: null }])).toEqual([]);
  });

  it("citation erasure emits and mechanically restores a theorem-local scope footnote", () => {
    const cited: FormalBlock = {
      ...block,
      cited_dependencies: [{
        node_id: "lem:published",
        cite_id: "cite:smith-2025",
        cite_key: "Smith2025",
        locator: "Theorem 2",
        statement: "Published lower bound.",
        status: "matched",
      }],
    };
    const rendered = blocksToTex([cited]);
    expect(rendered).not.toContain("\\begin{citedv}");
    expect(rendered).toContain("[Main]*");
    expect(rendered).toContain("\\verificationfootnotetext{");
    expect(rendered).toContain("\\citep{Smith2025} (Theorem 2)");
    expect(rendered).toContain("If that cited conclusion is false");
    const stripped = rendered.replace(/\n?% CAUSALSMITH-CITED-SCOPE-BEGIN[\s\S]*?% CAUSALSMITH-CITED-SCOPE-END[^\n]*/g, "");
    expect(normalizeCitedScopeFootnotes(stripped, [cited])).toBe(rendered);
    expect(normalizeCitedScopeFootnotes(rendered, [cited])).toBe(rendered);
    const followedByProse = `${rendered}\nFollowing prose.`;
    expect(normalizeCitedScopeFootnotes(followedByProse, [cited])).toBe(followedByProse);
    const gluedByRevision = `${rendered}Following prose.`;
    expect(normalizeCitedScopeFootnotes(gluedByRevision, [cited])).toBe(followedByProse);
    const markerDropped = rendered.replace("[Main]*", "[Main]");
    expect(normalizeCitedScopeFootnotes(markerDropped, [cited])).toBe(rendered);
  });
});
