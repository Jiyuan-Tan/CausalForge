import { describe, it, expect } from "vitest";
import { execFileSync } from "node:child_process";
import { existsSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { dischargeStartStage, parseArgsForTest, tsxEsmSpecifier } from "../src/cli.js";

describe("cli --reopen parsing", () => {
  it("parses --reopen <qid> <spec>", () => {
    const a = parseArgsForTest(["--reopen", "exp_bipartite_minimax_design_v1", "v1"]);
    expect(a.reopenMode).toBe(true);
    expect(a.qid).toBe("exp_bipartite_minimax_design_v1");
    expect(a.specialization).toBe("v1");
  });

  it("rejects --reopen without a spec", () => {
    expect(() => parseArgsForTest(["--reopen", "exp_foo"])).toThrow();
  });

  it("rejects --reopen with extra positionals", () => {
    expect(() => parseArgsForTest(["--reopen", "exp_foo", "v1", "extra"])).toThrow();
  });
});

describe("cli --discharge-gate parsing", () => {
  it("parses --discharge-gate <qid> <spec> <node_id>", () => {
    const a = parseArgsForTest([
      "--discharge-gate",
      "exp_bipartite_minimax_design_v1",
      "v1",
      "thm:heterogeneity-separation:EnvelopeLineC2Data",
    ]);
    expect(a.dischargeGateMode).toBe(true);
    expect(a.qid).toBe("exp_bipartite_minimax_design_v1");
    expect(a.specialization).toBe("v1");
    expect(a.dischargeGateNode).toBe("thm:heterogeneity-separation:EnvelopeLineC2Data");
  });

  it("carries an explicit --from-stage override through parse", () => {
    const a = parseArgsForTest([
      "--discharge-gate", "exp_foo", "v1", "node", "--from-stage", "F4",
    ]);
    expect(a.dischargeGateMode).toBe(true);
    expect(a.dischargeGateNode).toBe("node");
    expect(a.fromStage).toBe("F4");
  });

  it("rejects --discharge-gate without a node id", () => {
    expect(() => parseArgsForTest(["--discharge-gate", "exp_foo", "v1"])).toThrow();
  });

  it("rejects --discharge-gate with extra positionals", () => {
    expect(() =>
      parseArgsForTest(["--discharge-gate", "exp_foo", "v1", "node", "extra"]),
    ).toThrow();
  });
});

describe("tsxEsmSpecifier", () => {
  // REGRESSION. `--discharge-gate` step 2 spawns `node --import <spec> bin/gate.ts` with
  // `cwd: repoRoot` (the CausalSmith package dir) so gate.ts's own findRepoRoot lands on the
  // package. But tsx is installed under `tools/`, NOT at repoRoot — so the bare specifier
  // `tsx/esm` resolved against the child's cwd and died ERR_MODULE_NOT_FOUND, killing the
  // fused discharge before it ever reached the pipeline. Every prior test here was pure
  // arg-parsing, so nothing caught it.
  it("resolves to an existing file URL", () => {
    const spec = tsxEsmSpecifier();
    expect(spec.startsWith("file://")).toBe(true);
    expect(existsSync(fileURLToPath(spec))).toBe(true);
  });

  // The load-bearing property: a child launched from a cwd where `tsx` does NOT resolve must
  // still be able to load a TypeScript entrypoint. A bare "tsx/esm" fails this.
  it("lets `node --import <spec> foo.ts` run from a cwd that cannot resolve tsx", () => {
    const dir = mkdtempSync(path.join(tmpdir(), "tsx-spec-"));
    const entry = path.join(dir, "entry.ts");
    writeFileSync(entry, "const n: number = 41;\nconsole.log(n + 1);\n");
    const out = execFileSync(process.execPath, ["--import", tsxEsmSpecifier(), entry], {
      cwd: dir, // no node_modules anywhere up this tree
      encoding: "utf8",
    });
    expect(out.trim()).toBe("42");
  });
});

describe("dischargeStartStage", () => {
  it("defaults to F2.5 so the delta/added-premise review re-runs on reopened consumers", () => {
    expect(dischargeStartStage(undefined)).toBe("F2.5");
  });

  // F3/F3.5/F4 are no-op pass-throughs — all proof and review work moved into the F2.5 loop.
  // Entering at one of them ungates the plan/graph (dropping the hypothesis) and then runs NO
  // verification before F5 re-banks as `accepted`, while `gate.ts --ungate` never touches the
  // .lean (F2 re-scaffolds the hypothesis). That re-banks a still-conditional theorem as
  // unconditional, so these entry points must be refused rather than honored.
  it.each(["F3", "F3.5", "F4"] as const)("refuses the pass-through entry stage %s", (stage) => {
    expect(() => dischargeStartStage(stage)).toThrow(/pass-through|no verification|F2\.5/i);
  });

  it("honors an override that still runs verification", () => {
    expect(dischargeStartStage("F2.5")).toBe("F2.5");
    expect(dischargeStartStage("F2")).toBe("F2");
  });
});
