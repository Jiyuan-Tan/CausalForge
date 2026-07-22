import { describe, expect, it } from "vitest";
import { parseArgsForTest } from "../src/cli.js";
import { mkdir, mkdtemp, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { assertUpgradeNoveltyTarget, loadParentEntry } from "../src/upgrade.js";

describe("cli --upgrade parsing", () => {
  it("parses --upgrade with --upgrade-axis and --novelty flagship", () => {
    const args = parseArgsForTest([
      "--propose", "Dynamic IV bounds upgrade",
      "--novelty", "flagship",
      "--upgrade", "pid_dynamic_iv_compliance_v2",
      "--upgrade-axis", "estimation",
      "pid_dynamic_iv_compliance", "v3",
    ]);
    expect(args.upgradeFrom).toEqual({
      parent_qid: "pid_dynamic_iv_compliance",
      parent_spec: "v2",
      parent_tier: "accepted",
      upgrade_axis: "estimation",
    });
    expect(args.noveltyTarget).toBe("flagship");
  });

  it("parses a non-flagship upgrade target for parent-aware validation", () => {
    const args = parseArgsForTest([
      "--propose", "x",
      "--novelty", "field",
      "--upgrade", "pid_foo_v1",
      "--upgrade-axis", "computation",
      "qid", "spec",
    ]);
    expect(args.noveltyTarget).toBe("field");
    expect(args.upgradeFrom?.parent_qid).toBe("pid_foo");
  });

  it("rejects --upgrade without an explicit novelty target", () => {
    expect(() => parseArgsForTest([
      "--propose", "x",
      "--upgrade", "pid_foo_v1",
      "--upgrade-axis", "computation",
      "qid", "spec",
    ])).toThrow(/requires --novelty/);
  });

  it("rejects --upgrade without --upgrade-axis", () => {
    expect(() =>
      parseArgsForTest([
        "--propose", "x",
        "--novelty", "flagship",
        "--upgrade", "pid_foo_v1",
        "qid", "spec",
      ]),
    ).toThrow(/upgrade-axis/);
  });

  it("rejects --upgrade-axis with bad value", () => {
    expect(() =>
      parseArgsForTest([
        "--propose", "x",
        "--novelty", "flagship",
        "--upgrade", "pid_foo_v1",
        "--upgrade-axis", "polish",
        "qid", "spec",
      ]),
    ).toThrow(/upgrade-axis/);
  });
});

async function makeBankEntry(args: {
  repoRoot: string;
  tier: "accepted" | "downgraded";
  qid: string;
  spec: string;
  topic: string;
  cluster: "panel" | "exactid" | "partialid";
  bankedNoveltyTier?: "incremental" | "subfield" | "field" | "flagship";
  nestedLayout?: boolean;
}): Promise<string> {
  const entry = `${args.qid}_${args.spec}`;
  const dir = path.join(args.repoRoot, "doc", "research", "_bank", args.tier, entry);
  await mkdir(dir, { recursive: true });
  const readme =
    `---\nqid: ${args.qid}\nspec: ${args.spec}\ntopic: ${JSON.stringify(args.topic)}\n` +
    `novelty_target: field\nbanked_novelty_tier: ${args.bankedNoveltyTier ?? "field"}\n` +
    `tier_at_proposal: ACCEPT\ntier_at_derivation: ACCEPT\n` +
    `reusable_artifacts: []\nseeds_burned: []\nbanked_on: "2026-05-14"\n---\n\n# ${entry}\n`;
  await writeFile(path.join(dir, "README.md"), readme);
  await writeFile(
    path.join(dir, args.nestedLayout ? "state.json" : `${entry}_state.json`),
    JSON.stringify({
      stage_completed: "0.5",
      proposed_from: {
        topic: args.topic,
        novelty_target: "field",
        cluster: args.cluster,
        literature_map: "Manski 1990; Balke-Pearl 1997; ...",
      },
    }),
  );
  const proposalPath = args.nestedLayout
    ? path.join(dir, "discovery", "proposal.tex")
    : path.join(dir, `${entry}_proposal.tex`);
  const derivationPath = args.nestedLayout
    ? path.join(dir, "discovery", "writeup.tex")
    : path.join(dir, `${entry}.tex`);
  await mkdir(path.dirname(proposalPath), { recursive: true });
  await writeFile(
    proposalPath,
    `\\section{Setup} parent proposal body for ${entry}\n`,
  );
  await writeFile(
    derivationPath,
    `\\section{Derivation} parent derivation body for ${entry}\n`,
  );
  return dir;
}

describe("loadParentEntry", () => {
  it("loads an accepted-tier parent", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-upgrade-"));
    await makeBankEntry({
      repoRoot,
      tier: "accepted",
      qid: "pid_x",
      spec: "v1",
      topic: "Bounds for dynamic IV",
      cluster: "partialid",
    });
    const parent = await loadParentEntry(repoRoot, {
      parent_qid: "pid_x",
      parent_spec: "v1",
    });
    expect(parent.tier).toBe("accepted");
    expect(parent.banked_novelty_tier).toBe("field");
    expect(parent.topic).toBe("Bounds for dynamic IV");
    expect(parent.cluster).toBe("partialid");
    expect(parent.proposal_tex).toContain("parent proposal body");
    expect(parent.derivation_tex).toContain("parent derivation body");
    expect(parent.literature_map).toMatch(/Manski/);
  });

  it("loads a downgraded-tier parent (re-test escape hatch)", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-upgrade-"));
    await makeBankEntry({
      repoRoot,
      tier: "downgraded",
      qid: "pid_dg",
      spec: "v1",
      topic: "Topic DG",
      cluster: "partialid",
      bankedNoveltyTier: "subfield",
    });
    const parent = await loadParentEntry(repoRoot, {
      parent_qid: "pid_dg",
      parent_spec: "v1",
    });
    expect(parent.tier).toBe("downgraded");
    expect(parent.banked_novelty_tier).toBe("subfield");
  });

  it("loads current nested bank artifacts", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-upgrade-"));
    await makeBankEntry({
      repoRoot,
      tier: "downgraded",
      qid: "stat_nested",
      spec: "v1",
      topic: "Nested bank topic",
      cluster: "partialid",
      bankedNoveltyTier: "subfield",
      nestedLayout: true,
    });
    const parent = await loadParentEntry(repoRoot, {
      parent_qid: "stat_nested",
      parent_spec: "v1",
    });
    expect(parent.proposal_tex).toContain("parent proposal body");
    expect(parent.derivation_tex).toContain("parent derivation body");
    expect(parent.banked_novelty_tier).toBe("subfield");
  });

  it("accepts only novelty targets strictly above the parent's banked tier", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-upgrade-"));
    await makeBankEntry({
      repoRoot,
      tier: "downgraded",
      qid: "stat_parent",
      spec: "v1",
      topic: "Parent",
      cluster: "partialid",
      bankedNoveltyTier: "subfield",
    });
    const parent = await loadParentEntry(repoRoot, {
      parent_qid: "stat_parent",
      parent_spec: "v1",
    });
    expect(assertUpgradeNoveltyTarget("field", parent)).toBe("field");
    expect(assertUpgradeNoveltyTarget("flagship", parent)).toBe("flagship");
    expect(() => assertUpgradeNoveltyTarget("subfield", parent)).toThrow(/strictly above/);
    expect(() => assertUpgradeNoveltyTarget("incremental", parent)).toThrow(/strictly above/);
  });

  it("rejects parents in failed/legacy tiers", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-upgrade-"));
    const dir = path.join(repoRoot, "doc", "research", "_bank", "failed", "pid_z_v1");
    await mkdir(dir, { recursive: true });
    await writeFile(
      path.join(dir, "README.md"),
      `---\nqid: pid_z\nspec: v1\ntopic: "Z"\n---\n`,
    );
    await expect(
      loadParentEntry(repoRoot, { parent_qid: "pid_z", parent_spec: "v1" }),
    ).rejects.toThrow(/accepted or downgraded/);
  });

  it("errors when parent is not found", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-upgrade-"));
    await expect(
      loadParentEntry(repoRoot, { parent_qid: "nope", parent_spec: "v1" }),
    ).rejects.toThrow(/not found/);
  });
});
