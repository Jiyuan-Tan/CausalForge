import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { execFile } from "node:child_process";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { promisify } from "node:util";
import os from "node:os";
import path from "node:path";

const exec = promisify(execFile);
const __dirname = path.dirname(fileURLToPath(import.meta.url));
const TOOLS_ROOT = path.resolve(__dirname, "..");
const DOC_GEN = path.resolve(TOOLS_ROOT, "bin", "library_doc_gen.ts");

let repoRoot: string;

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "library-doc-gen-"));
  await mkdir(path.join(repoRoot, "doc", "library_review"), { recursive: true });
  await writeFile(
    path.join(repoRoot, "doc", "library_index.json"),
    JSON.stringify({
      commit: "abcdef1",
      // Every leaf module needs a docstring: the description gate covers leaf
      // pages, not just their ancestor namespaces. Tests that exercise a
      // specific failure blank only the entry they are about.
      modules: { "Causalean.Graph.DAG": "The DAG module." },
      entries: [
        {
          name: "Causalean.Graph.DAG.foo",
          statement: "Nat",
          doc: "Foo declaration.",
          module: "Causalean.Graph.DAG",
          line: 1,
          kind: "def",
        },
      ],
    }),
    "utf8",
  );
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

async function runDocGen(args: string[]): Promise<void> {
  await exec(process.execPath, ["--import", "tsx/esm", DOC_GEN, ...args], {
    cwd: TOOLS_ROOT,
    env: { ...process.env },
  });
}

// Each case spawns library_doc_gen as a real subprocess (node + tsx, ~4s per
// call) and several call it twice, so the 5s vitest default is not survivable.
describe("library_doc_gen", { timeout: 60_000 }, () => {
  it("refuses to regenerate a theorem-bearing file without a curated theorem anchor", async () => {
    const indexPath = path.join(repoRoot, "doc", "library_index.json");
    const index = JSON.parse(await readFile(indexPath, "utf8"));
    index.entries.push({
      name: "Causalean.Graph.Result.main",
      statement: "True",
      doc: "The main result.",
      module: "Causalean.Graph.Result",
      file: "Causalean/Graph/Result.lean",
      line: 1,
      kind: "theorem",
    });
    // Describe the leaf, so the missing curated theorem anchor is the only
    // reason this fixture can fail.
    index.modules["Causalean.Graph.Result"] = "The result module.";
    await writeFile(indexPath, JSON.stringify(index), "utf8");
    const apiPath = path.join(repoRoot, "doc", "API.md");
    await writeFile(apiPath, "<!-- GEN:Causalean.Graph.DAG -->\nstale\n<!-- /GEN -->\n", "utf8");

    await expect(runDocGen(["--root", repoRoot, "--api", apiPath, "--write"])).rejects.toMatchObject({
      stderr: expect.stringContaining("Causalean/Graph/Result.lean"),
    });

    await writeFile(
      path.join(repoRoot, "doc", "library_review", "Graph.json"),
      JSON.stringify({
        headline_theorems: ["Causalean.Graph.Result.main"],
        reviews: [],
        flags: [],
      }),
      "utf8",
    );
    await runDocGen(["--root", repoRoot, "--api", apiPath, "--write"]);
  });

  it("refuses to regenerate when a published namespace page lacks a short description", async () => {
    const indexPath = path.join(repoRoot, "doc", "library_index.json");
    const index = JSON.parse(await readFile(indexPath, "utf8"));
    index.entries.push(
      {
        name: "Causalean.Graph.AlgebraicGeometry.first",
        statement: "Nat",
        doc: "First declaration.",
        module: "Causalean.Graph.AlgebraicGeometry.First",
        file: "Causalean/Graph/AlgebraicGeometry/First.lean",
        line: 1,
        kind: "def",
      },
      {
        name: "Causalean.Graph.AlgebraicGeometry.second",
        statement: "Nat",
        doc: "Second declaration.",
        module: "Causalean.Graph.AlgebraicGeometry.Second",
        file: "Causalean/Graph/AlgebraicGeometry/Second.lean",
        line: 1,
        kind: "def",
      },
    );
    // Describe both leaves, so the only page still lacking a description is the
    // intermediate namespace `Causalean.Graph.AlgebraicGeometry` under test.
    index.modules["Causalean.Graph.AlgebraicGeometry.First"] = "The first module.";
    index.modules["Causalean.Graph.AlgebraicGeometry.Second"] = "The second module.";
    await writeFile(indexPath, JSON.stringify(index), "utf8");
    const apiPath = path.join(repoRoot, "doc", "API.md");
    await writeFile(apiPath, "<!-- GEN:Causalean.Graph.DAG -->\nstale\n<!-- /GEN -->\n", "utf8");

    await expect(runDocGen(["--root", repoRoot, "--api", apiPath, "--write"])).rejects.toMatchObject({
      stderr: expect.stringContaining("Causalean.Graph.AlgebraicGeometry"),
    });

    await writeFile(
      path.join(repoRoot, "doc", "library_review", "Graph.json"),
      JSON.stringify({
        headline_theorems: [],
        reviews: [],
        flags: [],
        namespace_intros: { AlgebraicGeometry: "Algebraic-geometry helpers." },
      }),
      "utf8",
    );
    await runDocGen(["--root", repoRoot, "--api", apiPath, "--write"]);
  });

  it("refuses to regenerate when a published declaration lacks a natural-language translation", async () => {
    const indexPath = path.join(repoRoot, "doc", "library_index.json");
    const index = JSON.parse(await readFile(indexPath, "utf8"));
    index.entries.push({
      name: "Causalean.Graph.DAG.undocumented",
      statement: "Nat",
      doc: null,
      module: "Causalean.Graph.DAG",
      file: "Causalean/Graph/DAG.lean",
      line: 2,
      kind: "def",
    });
    await writeFile(indexPath, JSON.stringify(index), "utf8");
    const apiPath = path.join(repoRoot, "doc", "API.md");
    await writeFile(apiPath, "<!-- GEN:Causalean.Graph.DAG -->\nstale\n<!-- /GEN -->\n", "utf8");

    await expect(runDocGen(["--root", repoRoot, "--api", apiPath, "--write"])).rejects.toMatchObject({
      stderr: expect.stringContaining("Causalean.Graph.DAG.undocumented"),
    });

    index.entries.at(-1).source = "/-- An explicitly documented declaration. -/\ndef undocumented : Nat := 0";
    await writeFile(indexPath, JSON.stringify(index), "utf8");
    await runDocGen(["--root", repoRoot, "--api", apiPath, "--write"]);
  });

  it("ignores inline marker examples in API prose", async () => {
    const apiPath = path.join(repoRoot, "doc", "API.md");
    await writeFile(
      apiPath,
      [
        "# API",
        "",
        "Per-decl tables live inside `<!-- GEN:<module> -->` ... `<!-- /GEN -->` markers.",
        "",
        "### Declarations",
        "",
        "<!-- GEN:Causalean.Graph.DAG -->",
        "stale",
        "<!-- /GEN -->",
        "",
      ].join("\n"),
      "utf8",
    );

    await runDocGen(["--root", repoRoot, "--api", apiPath, "--write"]);

    const out = await readFile(apiPath, "utf8");
    expect(out).toContain("`<!-- GEN:<module> -->`");
    expect(out).toContain("Per-decl tables live inside");
    expect(out).toContain("| `Graph.DAG.foo` | `Nat` | Foo declaration. |");
    expect(out).not.toContain("_(no documented declarations in <module>)_");
  });
});
