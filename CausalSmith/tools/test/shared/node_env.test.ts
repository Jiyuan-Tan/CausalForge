// CausalSmith/tools/test/shared/node_env.test.ts
//
// Regression guard for scripts/node_env.sh, the single Node resolver every
// launcher (codex.ts, the skills, the docs) sources.
//
// The bug it replaced: launchers hardcoded `source ~/.nvm/nvm.sh && nvm use
// 20.20.2`. Where $NVM_DIR points outside $HOME, `~/.nvm/nvm.sh` does not
// exist, so guarded call sites silently no-opped (leaving an arbitrary Node on
// PATH, which then tripped "resolved to Node 22 despite nvm use") and unguarded
// ones aborted the `&&` chain outright. These tests pin both halves of the fix:
// $HOME is never assumed, and any Node at or above the engines floor is
// accepted rather than one exact patch release.
import { describe, it, expect } from "vitest";
import { execFile } from "node:child_process";
import { mkdtemp, rm, writeFile, chmod, mkdir } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { promisify } from "node:util";

const execFileAsync = promisify(execFile);

const TOOLS_ROOT = path.resolve(__dirname, "..", "..");
const SCRIPT = path.join(TOOLS_ROOT, "scripts", "node_env.sh");

/** Run `source node_env.sh` in a clean bash and report the Node it selected. */
async function runResolver(env: NodeJS.ProcessEnv): Promise<{
  code: number;
  nodePath: string;
  version: string;
  stderr: string;
}> {
  // `|| true` on the source keeps the reporting `echo`s running on failure so a
  // failing case still yields a readable receipt instead of an opaque throw.
  const script = `
    source ${JSON.stringify(SCRIPT)}
    rc=$?
    echo "RC=$rc"
    echo "WHICH=$(command -v node 2>/dev/null)"
    echo "VERSION=$(node -v 2>/dev/null)"
    exit 0
  `;
  const { stdout, stderr } = await execFileAsync("bash", ["-c", script], { env });
  const field = (k: string) => new RegExp(`^${k}=(.*)$`, "m").exec(stdout)?.[1] ?? "";
  return {
    code: Number(field("RC")),
    nodePath: field("WHICH"),
    version: field("VERSION"),
    stderr,
  };
}

/** A directory holding a `node` stub that reports `version`. */
async function fakeNodeBin(root: string, name: string, version: string): Promise<string> {
  const bin = path.join(root, name, "bin");
  await mkdir(bin, { recursive: true });
  const stub = path.join(bin, "node");
  await writeFile(stub, `#!/bin/sh\necho ${version}\n`, "utf8");
  await chmod(stub, 0o755);
  return bin;
}

describe("scripts/node_env.sh", () => {
  it("keeps a PATH node that already satisfies the engines floor", async () => {
    const real = path.dirname(process.execPath);
    const res = await runResolver({
      PATH: `${real}:/usr/bin:/bin`,
      HOME: "/nonexistent-home",
      // No NVM_DIR: nothing to fall back to, so a pass proves the PATH node was accepted.
    });
    expect(res.code).toBe(0);
    expect(res.version).toBe(process.version);
  });

  it("does NOT assume $HOME — resolves via $NVM_DIR when ~/.nvm is absent", async () => {
    // The exact production shape: $HOME has no .nvm, $NVM_DIR is elsewhere, and
    // no usable node is on PATH. The old `~/.nvm/nvm.sh` prelude failed here.
    const tmp = await mkdtemp(path.join(os.tmpdir(), "nodeenv-nvmdir-"));
    try {
      const nvmDir = path.join(tmp, "nvm");
      await fakeNodeBin(path.join(nvmDir, "versions", "node"), "v22.9.9", "v22.9.9");
      const res = await runResolver({
        PATH: "/usr/bin:/bin",
        HOME: path.join(tmp, "home-without-nvm"),
        NVM_DIR: nvmDir,
      });
      expect(res.code).toBe(0);
      expect(res.version).toBe("v22.9.9");
    } finally {
      await rm(tmp, { recursive: true, force: true });
    }
  });

  it("replaces a too-old PATH node instead of accepting it", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "nodeenv-old-"));
    try {
      const oldBin = await fakeNodeBin(tmp, "ancient", "v12.22.9");
      const nvmDir = path.join(tmp, "nvm");
      await fakeNodeBin(path.join(nvmDir, "versions", "node"), "v20.20.2", "v20.20.2");
      const res = await runResolver({
        PATH: `${oldBin}:/usr/bin:/bin`,
        HOME: path.join(tmp, "home-without-nvm"),
        NVM_DIR: nvmDir,
      });
      expect(res.code).toBe(0);
      expect(res.version).toBe("v20.20.2");
    } finally {
      await rm(tmp, { recursive: true, force: true });
    }
  });

  it("accepts any major above the floor, not just the historically pinned 20.20.2", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "nodeenv-newest-"));
    try {
      const versions = path.join(tmp, "nvm", "versions", "node");
      await fakeNodeBin(versions, "v20.20.2", "v20.20.2");
      await fakeNodeBin(versions, "v22.23.2", "v22.23.2");
      await fakeNodeBin(versions, "v18.0.0", "v18.0.0"); // below floor, must be ignored
      const res = await runResolver({
        PATH: "/usr/bin:/bin",
        HOME: path.join(tmp, "home-without-nvm"),
        NVM_DIR: path.join(tmp, "nvm"),
      });
      expect(res.code).toBe(0);
      // Newest satisfying version wins; the sub-floor install is never selected.
      expect(res.version).toBe("v22.23.2");
    } finally {
      await rm(tmp, { recursive: true, force: true });
    }
  });

  it("fails closed with an actionable message when nothing satisfies the floor", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "nodeenv-none-"));
    try {
      const oldBin = await fakeNodeBin(tmp, "ancient", "v12.22.9");
      const nvmDir = path.join(tmp, "nvm");
      await fakeNodeBin(path.join(nvmDir, "versions", "node"), "v18.0.0", "v18.0.0");
      const res = await runResolver({
        PATH: `${oldBin}:/usr/bin:/bin`,
        HOME: path.join(tmp, "home-without-nvm"),
        NVM_DIR: nvmDir,
      });
      // Nonzero return is what makes `source node_env.sh && <cmd>` fail closed
      // rather than launching the pipeline on an unusable interpreter.
      expect(res.code).toBe(1);
      expect(res.stderr).toMatch(/no Node >=/);
      expect(res.stderr).toMatch(/CAUSALSMITH_NODE_BIN/);
    } finally {
      await rm(tmp, { recursive: true, force: true });
    }
  });

  it("honours the CAUSALSMITH_NODE_BIN override and clears npm_config_prefix", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "nodeenv-override-"));
    try {
      const forced = await fakeNodeBin(tmp, "forced", "v21.1.1");
      const script = `
        export npm_config_prefix=/bogus
        source ${JSON.stringify(SCRIPT)}
        echo "RC=$?"
        echo "VERSION=$(node -v)"
        echo "PREFIX=[\${npm_config_prefix:-unset}]"
        exit 0
      `;
      const { stdout } = await execFileAsync("bash", ["-c", script], {
        env: {
          PATH: "/usr/bin:/bin",
          HOME: path.join(tmp, "home-without-nvm"),
          CAUSALSMITH_NODE_BIN: forced,
        },
      });
      expect(stdout).toMatch(/RC=0/);
      expect(stdout).toMatch(/VERSION=v21\.1\.1/);
      // nvm and `npm --prefix tools` both misbehave when npm_config_prefix is set.
      expect(stdout).toMatch(/PREFIX=\[unset\]/);
    } finally {
      await rm(tmp, { recursive: true, force: true });
    }
  });

  it("reads the floor from package.json rather than hardcoding it", async () => {
    const { stderr } = await execFileAsync("bash", ["-c", `source ${JSON.stringify(SCRIPT)}`], {
      env: { ...process.env, CAUSALSMITH_NODE_ENV_VERBOSE: "1" },
    });
    const pkg = JSON.parse(
      await (await import("node:fs/promises")).readFile(path.join(TOOLS_ROOT, "package.json"), "utf8"),
    );
    const floor = String(pkg.engines.node).replace(/^>=\s*/, "");
    expect(stderr).toContain(`floor >=${floor}`);
  });
});
