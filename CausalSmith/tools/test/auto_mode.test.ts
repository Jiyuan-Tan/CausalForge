import { describe, expect, it } from "vitest";
import { parseArgsForTest } from "../src/cli.js";
import { checkpointGuidance } from "../src/checkpoint_playbook.js";

describe("--auto flag parsing", () => {
  it("defaults auto to false", () => {
    const args = parseArgsForTest(["pid_foo", "v1"]);
    expect(args.auto).toBe(false);
  });

  it("parses --auto and strips it from positionals", () => {
    const args = parseArgsForTest(["--auto", "pid_foo", "v1"]);
    expect(args.auto).toBe(true);
    expect(args.qid).toBe("pid_foo");
    expect(args.specialization).toBe("v1");
  });

  it("parses --auto alongside --resume", () => {
    const args = parseArgsForTest(["--resume", "--auto", "pid_foo", "v1"]);
    expect(args.auto).toBe(true);
    expect(args.resume).toBe(true);
  });
});

describe("checkpointGuidance auto banner", () => {
  it("omits the banner when not in auto mode", () => {
    const g = checkpointGuidance("1.5", "checkpoint", {}, false);
    expect(g).toBeDefined();
    expect(g).not.toContain("AUTO MODE");
  });

  it("prepends the 'decide and resume' banner on a pre-F5 checkpoint in auto mode", () => {
    const g = checkpointGuidance("1.5", "checkpoint", {}, true)!;
    expect(g).toContain("AUTO MODE");
    expect(g).toContain("without asking the user");
    // still carries the per-stage guidance body
    expect(g).toContain("CONSOLIDATED CKPT 1");
  });

  it("uses the DESIGNATED-STOP banner at F5 (CKPT 2) in auto mode", () => {
    const g = checkpointGuidance("5", "checkpoint", {}, true)!;
    expect(g).toContain("designated stop");
    expect(g).toContain("wait for user approval");
    expect(g).not.toContain("WITHOUT asking the user");
  });

  it("returns undefined on ordinary completed transitions regardless of auto", () => {
    expect(checkpointGuidance("1.5", "completed", {}, true)).toBeUndefined();
  });
});

describe("checkpointGuidance D0.5 verdict branching (not always PASS)", () => {
  const pass =
    'Stage 0.5 (typed) PASS after 1 directed-revise round(s) — D0.5.G tier=field ≥ floor=field (target=field). CKPT (D0.5→F1 go/no-go)';
  const nonconv =
    "Stage 0.5 (typed) non-converging — D0.R round 2 made no net progress. Open findings: frontier_overclaim@thm:x";
  const belowFloor =
    "Stage 0.5 (typed) BELOW NOVELTY FLOOR — D0.5.G tier=subfield < floor=field (target=field).";

  it("emits the PASS go/no-go guidance only on a genuine PASS message", () => {
    const g = checkpointGuidance("0.5", "checkpoint", {}, false, pass)!;
    expect(g).toContain("D0.5 PASS");
    expect(g).toContain("F1–F5");
  });

  it("emits NON-CONVERGING guidance (not PASS) on a non-converging halt", () => {
    const g = checkpointGuidance("0.5", "checkpoint", {}, false, nonconv)!;
    expect(g).toContain("NON-CONVERGING");
    expect(g).toContain("not a pass");
    expect(g).not.toContain("D0.5 PASS");
    expect(g).toContain("F1 waits");
  });

  it("emits BELOW-FLOOR guidance (not PASS) on a below-floor halt", () => {
    const g = checkpointGuidance("0.5", "checkpoint", {}, false, belowFloor)!;
    expect(g).toContain("BELOW NOVELTY FLOOR");
    expect(g).toContain("not a pass");
    expect(g).not.toContain("cleared the math panel AND the novelty floor");
  });

  it("does NOT assume PASS when the message is empty/unknown", () => {
    const g = checkpointGuidance("0.5", "checkpoint", {}, false, "")!;
    expect(g).toContain("read its message");
    expect(g).not.toContain("D0.5 PASS —");
  });

  it("keeps all auto-mode guidance compact", () => {
    const cases: Array<[Parameters<typeof checkpointGuidance>[0], string, string]> = [
      ["-0.5", "", ""],
      ["0", "", ""],
      ["0.5", pass, ""],
      ["0.5", nonconv, ""],
      ["0.5", belowFloor, ""],
      ["1", "", "substrate_build_required"],
      ["1.5", "", ""],
      ["2.5", "", ""],
      ["5", "", ""],
    ];
    for (const [stage, message, substrateBuild] of cases) {
      const guidance = checkpointGuidance(
        stage,
        "checkpoint",
        substrateBuild ? { substrate_build_required: substrateBuild } : {},
        true,
        message,
      )!;
      expect(guidance.length).toBeLessThan(800);
    }
  });
});
