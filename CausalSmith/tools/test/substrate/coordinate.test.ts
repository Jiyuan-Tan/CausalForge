// CausalSmith/tools/test/substrate/coordinate.test.ts
import { describe, it, expect } from "vitest";
import {
  applyInsertOnly, applyManifest, insertImportSorted, type CoordinateApplyDeps,
} from "../../src/substrate/coordinate.js";
import type { CoordinationManifest } from "../../src/substrate/types.js";

/** In-memory fs + fake integration runner. `failStep` (a substring) makes the
 *  matching gate command return a nonzero code, triggering rollback. */
function memFs(initial: Record<string, string>) {
  const files = new Map<string, string>(Object.entries(initial));
  const runLog: string[] = [];
  let failStep: string | null = null;
  let timeoutStep: string | null = null;
  const deps: CoordinateApplyDeps = {
    run: async (cmd) => {
      runLog.push(cmd);
      // A watchdog-killed step reports timedOut (exitCode null upstream). It must
      // NOT be treated like a genuine build failure.
      if (timeoutStep && cmd.includes(timeoutStep)) return { code: 1, log: `timed out ${cmd}`, timedOut: true };
      return { code: failStep && cmd.includes(failStep) ? 1 : 0, log: `ran ${cmd}` };
    },
    readFile: async (p) => {
      const v = files.get(p);
      if (v === undefined) throw new Error(`ENOENT ${p}`);
      return v;
    },
    writeFile: async (p, t) => { files.set(p, t); },
    removeFile: async (p) => { files.delete(p); },
    removeDir: async () => {},
    exists: async (p) => files.has(p) || [...files.keys()].some((f) => f.startsWith(`${p}/`)),
  };
  return {
    files, deps, runLog,
    setFail: (s: string | null) => { failStep = s; },
    setTimeout: (s: string | null) => { timeoutStep = s; },
  };
}

const C_ROOT = "/c";
const ROOT_LEAN = "/c/Causalean.lean";
const STAGING = "/stage";

describe("applyInsertOnly", () => {
  it("inserts root imports in sorted order and idempotently", () => {
    const root = "import Causalean.A\nimport Causalean.C\n";
    const once = insertImportSorted(root, "import Causalean.B");
    expect(once).toBe("import Causalean.A\nimport Causalean.B\nimport Causalean.C\n");
    expect(insertImportSorted(once, "import Causalean.B")).toBe(once);
  });

  it("inserts after the anchor line, preserving existing bytes", () => {
    const orig = "import A\n\nnamespace N\n-- decls here\nend N\n";
    const { merged, at, segment } = applyInsertOnly(orig, "-- decls here", "theorem t : True := trivial");
    expect(merged).toContain("theorem t : True := trivial");
    // Byte-preservation: removing the inserted segment at its offset reproduces orig.
    expect(merged.slice(0, at) + merged.slice(at + segment.length)).toBe(orig);
    // The insertion lands after the anchor line, before `end N`.
    expect(merged.indexOf("theorem t")).toBeGreaterThan(merged.indexOf("-- decls here"));
    expect(merged.indexOf("theorem t")).toBeLessThan(merged.indexOf("end N"));
  });

  it("appends at end of file for an empty anchor", () => {
    const orig = "import A\n";
    const { merged, at, segment } = applyInsertOnly(orig, "", "def z := 0");
    expect(merged.startsWith(orig)).toBe(true);
    expect(merged).toContain("def z := 0");
    expect(merged.slice(0, at) + merged.slice(at + segment.length)).toBe(orig);
  });

  it("throws when the anchor is not present", () => {
    expect(() => applyInsertOnly("import A\n", "nope", "x")).toThrow(/anchor not found/);
  });
});

describe("applyManifest", () => {
  // Base tree + staged bodies (codex writes bodies under STAGING; manifest only
  // references them by `from`).
  const base = () => ({
    [ROOT_LEAN]: "import Causalean.Mathlib.Foo\n",
    "/c/Causalean/Mathlib/Foo.lean": "namespace Foo\n-- add here\nend Foo\n",
    "/stage/bar.lean": "namespace Bar\nend Bar\n",
    "/stage/merge_foo.lean": "theorem t : True := trivial",
  });

  it("applies create_file + merge_lean, root-wires the new module, cleans staging", async () => {
    const fs = memFs(base());
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [
        { kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" },
        { kind: "merge_lean", target: "Causalean/Mathlib/Foo.lean", anchor: "-- add here", from: "merge_foo.lean" },
      ],
    };
    const staging = "/c/CausalSmith/CausalSmith/Substrate/S/Basic.lean";
    fs.files.set(staging, "stub");
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [staging], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(true);
    // New file written, existing file merged (existing bytes intact), root wired.
    expect(fs.files.get("/c/Causalean/Mathlib/Bar.lean")).toContain("namespace Bar");
    expect(fs.files.get("/c/Causalean/Mathlib/Foo.lean")).toContain("theorem t");
    expect(fs.files.get("/c/Causalean/Mathlib/Foo.lean")).toContain("namespace Foo");
    expect(fs.files.get(ROOT_LEAN)).toContain("import Causalean.Mathlib.Bar");
    // Staging source deleted on success.
    expect(fs.files.has(staging)).toBe(false);
    // The full gate ran.
    expect(fs.runLog.some((c) => c.includes("lake build"))).toBe(true);
    expect(fs.runLog.some((c) => c.includes("doc:check"))).toBe(true);
  });

  it("rolls back ALL changes when a gate step fails", async () => {
    const fs = memFs(base());
    fs.setFail("lake build");
    const origFoo = fs.files.get("/c/Causalean/Mathlib/Foo.lean");
    const origRoot = fs.files.get(ROOT_LEAN);
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [
        { kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" },
        { kind: "merge_lean", target: "Causalean/Mathlib/Foo.lean", anchor: "-- add here", from: "merge_foo.lean" },
      ],
    };
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    // Created file removed; merged file + root restored byte-for-byte.
    expect(fs.files.has("/c/Causalean/Mathlib/Bar.lean")).toBe(false);
    expect(fs.files.get("/c/Causalean/Mathlib/Foo.lean")).toBe(origFoo);
    expect(fs.files.get(ROOT_LEAN)).toBe(origRoot);
  });

  it("does NOT roll back when a gate step times out — preserves files and flags timedOut", async () => {
    const fs = memFs(base());
    fs.setTimeout("lake build"); // watchdog-killed verify step, not a real failure
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [
        { kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" },
        { kind: "merge_lean", target: "Causalean/Mathlib/Foo.lean", anchor: "-- add here", from: "merge_foo.lean" },
      ],
    };
    const staging = "/c/CausalSmith/CausalSmith/Substrate/S/Basic.lean";
    fs.files.set(staging, "stub");
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [staging], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    expect(res.timedOut).toBe(true);
    // Promoted work is PRESERVED (a timeout is not proof of failure): the new
    // file, the merge, and the root-wire all remain — a human confirms and
    // finalizes or rolls back manually.
    expect(fs.files.get("/c/Causalean/Mathlib/Bar.lean")).toContain("namespace Bar");
    expect(fs.files.get("/c/Causalean/Mathlib/Foo.lean")).toContain("theorem t");
    expect(fs.files.get(ROOT_LEAN)).toContain("import Causalean.Mathlib.Bar");
    // Promotion NOT finalized: the staging source is left in place.
    expect(fs.files.has(staging)).toBe(true);
  });

  it("refuses a manifest target that escapes the Causalean root (rollback, no gate)", async () => {
    const fs = memFs({ ...base(), "/stage/x.txt": "x" });
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "write_file", target: "../escape.txt", from: "x.txt" }],
    };
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    expect(res.log).toMatch(/escapes the Causalean root/);
    expect(fs.runLog.length).toBe(0); // never reached the gate
  });

  it("rejects a new Lean file outside an existing Causalean subject area", async () => {
    const fs = memFs(base());
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "create_file", target: "Causalean/NewArea/Bar.lean", from: "bar.lean", newModule: "Causalean.NewArea.Bar" }],
    };
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    expect(res.log).toMatch(/non-existing Causalean subject area/);
    expect(fs.runLog).toEqual([]);
  });

  it("rejects final Lean content with a CausalSmith dependency", async () => {
    const fs = memFs({ ...base(), "/stage/bar.lean": "import CausalSmith.Paper\nnamespace Bar\nend Bar\n" });
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
    };
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(false);
    expect(res.log).toMatch(/retains a CausalSmith dependency/);
    expect(fs.files.has("/c/Causalean/Mathlib/Bar.lean")).toBe(false);
    expect(fs.runLog).toEqual([]);
  });

  it("rejects namespace/open CausalSmith references even without an import", async () => {
    for (const body of ["namespace CausalSmith\nend CausalSmith\n", "open CausalSmith\n"]) {
      const fs = memFs({ ...base(), "/stage/bar.lean": body });
      const manifest: CoordinationManifest = {
        notes: "",
        ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
      };
      const res = await applyManifest(
        { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
        fs.deps,
      );
      expect(res.ok).toBe(false);
      expect(res.log).toMatch(/retains a CausalSmith dependency/);
    }
  });

  it("does not reject a CausalSmith name mentioned only in a comment or string", async () => {
    const fs = memFs({
      ...base(),
      "/stage/bar.lean": "/- migrated from CausalSmith.Old -/\ndef label := \"CausalSmith.Old\"\n",
    });
    const manifest: CoordinationManifest = {
      notes: "",
      ops: [{ kind: "create_file", target: "Causalean/Mathlib/Bar.lean", from: "bar.lean", newModule: "Causalean.Mathlib.Bar" }],
    };
    const res = await applyManifest(
      { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
      fs.deps,
    );
    expect(res.ok).toBe(true);
  });

  it("rejects merge and record writes outside their exact allowlists", async () => {
    const cases: CoordinationManifest[] = [
      { notes: "", ops: [{ kind: "merge_lean", target: "CausalSmith/Paper.lean", anchor: "", from: "merge_foo.lean" }] },
      { notes: "", ops: [{ kind: "write_file", target: "package.json", from: "bar.lean" }] },
      { notes: "", ops: [{ kind: "create_file", target: "docs/arbitrary.md", from: "bar.lean" }] },
    ];
    for (const manifest of cases) {
      const fs = memFs({ ...base(), "/c/CausalSmith/Paper.lean": "namespace Paper\n" });
      const res = await applyManifest(
        { cRoot: C_ROOT, repoRoot: "/c/CausalSmith", stagingDir: STAGING, leanFiles: [], manifest },
        fs.deps,
      );
      expect(res.ok).toBe(false);
      expect(fs.runLog).toEqual([]);
    }
  });
});
