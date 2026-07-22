import { describe, it, expect, vi } from "vitest";
import { main } from "../../bin/d0_apply_change.js";

async function invoke(args: string[]): Promise<{ code: number; stderr: string }> {
  const priorArgv = process.argv;
  const priorExitCode = process.exitCode;
  const stderr: string[] = [];
  const error = vi.spyOn(console, "error").mockImplementation((...values: unknown[]) => {
    stderr.push(values.map(String).join(" "));
  });
  try {
    process.argv = [process.execPath, "d0_apply_change.ts", ...args];
    process.exitCode = undefined;
    await main();
    return { code: Number(process.exitCode ?? 0), stderr: stderr.join("\n") };
  } finally {
    process.argv = priorArgv;
    process.exitCode = priorExitCode;
    error.mockRestore();
  }
}

describe("d0_apply_change — unknown flags", () => {
  it("refuses --dry-run instead of applying for real", async () => {
    // This CLI's preview flag is `--check`. `--dry-run` used to be silently ignored, so
    // the operator's safest-looking invocation performed an IRREVERSIBLE bundle apply —
    // rewriting the frozen proto and deleting statements — while printing "Applied N
    // change(s)", which reads exactly like a preview.
    const { code, stderr } = await invoke(["some_qid", "some_spec", "--all", "--dry-run"]);
    expect(code).not.toBe(0);
    expect(stderr).toMatch(/unrecognized flag/);
    expect(stderr).toMatch(/--dry-run/);
    expect(stderr).toMatch(/nothing was mutated/);
  }, 70000);

  it("names --check as the preview so the error is actionable", async () => {
    const { stderr } = await invoke(["some_qid", "some_spec", "--all", "--preview"]);
    expect(stderr).toMatch(/--check is the preview/);
  }, 70000);
});
