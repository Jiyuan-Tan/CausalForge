import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { buildLeanContextIndex } from "../src/presentation/lean_context.js";

let dir: string;
beforeEach(async () => {
  dir = await mkdtemp(join(tmpdir(), "leanctx-"));
});
afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

describe("buildLeanContextIndex", () => {
  it("returns a theorem's signature (not its proof) and inlines the local defs it references", async () => {
    await writeFile(
      join(dir, "M.lean"),
      [
        "def MarginTail (P : Law) (Cm u0 : ℝ) : Prop := True",
        "",
        "theorem rate_thm (P : Law) (Cm u0 cB : ℝ) (h : MarginTail P Cm u0)",
        "    (hcal : 8 * cB < Real.log 5) :",
        "    M P ≥ 1 := by",
        "  sorry",
      ].join("\n"),
      "utf8",
    );
    const idx = await buildLeanContextIndex(dir, ".");
    const ctx = await idx.contextFor({ decl_name: "rate_thm", file: "M.lean" });
    expect(ctx).not.toBeNull();
    expect(ctx!.statement).toContain("theorem rate_thm");
    expect(ctx!.statement).toContain("8 * cB < Real.log 5"); // load-bearing calibration in the signature
    expect(ctx!.statement).not.toContain("sorry"); // signature only, proof excluded
    expect(ctx!.referencedDefs).toContain("def MarginTail"); // the referenced def is inlined
    expect(ctx!.pointer).toContain("rate_thm");
  });

  it("returns null for a decl that does not resolve in the file", async () => {
    await writeFile(join(dir, "M.lean"), "def x : Nat := 1\n", "utf8");
    const idx = await buildLeanContextIndex(dir, ".");
    expect(await idx.contextFor({ decl_name: "nonexistent", file: "M.lean" })).toBeNull();
  });

  it("returns an empty referencedDefs when the statement references no local defs", async () => {
    await writeFile(join(dir, "M.lean"), "theorem t (n : Nat) (h : 0 < n) : True := by trivial\n", "utf8");
    const idx = await buildLeanContextIndex(dir, ".");
    const ctx = await idx.contextFor({ decl_name: "t", file: "M.lean" });
    expect(ctx).not.toBeNull();
    expect(ctx!.referencedDefs).toBe("");
  });
});
