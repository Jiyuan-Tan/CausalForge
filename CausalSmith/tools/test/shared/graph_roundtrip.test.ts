import { describe, it, expect } from "vitest";
import path from "node:path";
import { mkdtemp, writeFile, mkdir } from "node:fs/promises";
import { tmpdir } from "node:os";
import {
  buildIndex,
  loadAllNodes,
} from "../../src/shared/graph.js";
import type { Insight, Theorem } from "../../src/shared/kb_types.js";

function makeTheorem(overrides: Partial<Theorem> = {}): Theorem {
  return {
    schema_version: 2,
    theorem_id: "ins1_t1",
    parent_insight_id: "ins1",
    setup: "Let X, Y be random variables.",
    statement: "If A then B.",
    proof_sketch: "Apply lemma L.",
    proof_punchline: "By L.",
    cites_theorems: [],
    prerequisites: [],
    candidate_specializations: [],
    banked_by: [],
    verification_status: "unverified",
    ...overrides,
  };
}

function makeInsight(theorem_ids: string[]): Insight {
  return {
    schema_version: 2,
    insight_id: "ins1",
    title: "An insight",
    summary: "summary",
    background: {
      why_matters: "why",
      prior_approach: "prior",
      gap: "gap",
    },
    theorems: theorem_ids,
    extensions: [],
    verification_status: "unverified",
  };
}

describe("graph round-trip", () => {
  it("decomposes_into edge from Insight to Theorem appears in buildIndex.forward", async () => {
    const studyDir = await mkdtemp(path.join(tmpdir(), "td-graph-"));
    // Seed an Insight + Theorem pair under nodes/<type>/.
    await mkdir(path.join(studyDir, "nodes", "insight"), { recursive: true });
    await mkdir(path.join(studyDir, "nodes", "theorem"), { recursive: true });
    const insight = makeInsight(["ins1_t1"]);
    const theorem = makeTheorem();
    await writeFile(
      path.join(studyDir, "nodes", "insight", `${insight.insight_id}.json`),
      JSON.stringify(insight, null, 2),
      "utf8",
    );
    await writeFile(
      path.join(studyDir, "nodes", "theorem", `${theorem.theorem_id}.json`),
      JSON.stringify(theorem, null, 2),
      "utf8",
    );
    const nodes = await loadAllNodes(studyDir);
    expect(nodes).toHaveLength(2);
    const index = buildIndex(nodes);
    expect(index.counts.theorem).toBe(1);
    expect(index.counts.insight).toBe(1);
    const forward = index.forward[insight.insight_id];
    expect(forward).toBeDefined();
    expect(forward?.decomposes_into).toEqual([theorem.theorem_id]);
    // And reverse adjacency from theorem back to insight.
    const reverse = index.reverse[theorem.theorem_id];
    expect(reverse?.decomposes_into).toEqual([insight.insight_id]);
  });
});
