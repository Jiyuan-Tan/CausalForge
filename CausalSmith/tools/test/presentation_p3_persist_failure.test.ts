import { describe, it, expect } from "vitest";
import { mkdtemp, writeFile, readFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { stageP3 } from "../src/presentation/stages/p3_gates.js";
import { freshPaperState } from "../src/presentation/state.js";
import type { PaperState } from "../src/presentation/types.js";


const block = (obj_id: string, kind: string, env: string, body: string) => ({
  obj_id,
  alias: null,
  kind,
  env,
  title: null,
  body,
  ref_set: [],
  lean: null,
  status: "matched",
  provenance: "test",
  cited_dependencies: [],
  body_hash: "h",
});

const QID = "q_test";
const SPEC = "spec";

// \kappa is first USED in theorem T-1 but its notation-table home is definition P-1,
// which appears later in the file → trips the definition-order hard gate, the earliest
// failure exit in stageP3.
const PAPER = `
\\begin{theoremv}{T-1}[Rate]
The rate depends on \\kappa.
\\end{theoremv}
\\begin{definitionv}{P-1}[Kappa]
Let \\kappa be the exponent.
\\end{definitionv}
`;

const OUTLINE = `# Notation

| note symbol | symbol | meaning | home |
| --- | --- | --- | --- |
| kappa | \\(\\kappa\\) | exponent | P-1 |

# Sections
`;

describe("P3 persists its diagnosis before throwing", () => {
  // Regression: `pipeline.ts` only calls savePaperState AFTER a stage returns, so a stage
  // that recorded `hard_gate_failures` and then threw lost the record. Every run on disk
  // showed `hard_gate_failures: []` even when run_p3.log had the gate failing on 7
  // statements — the field was structurally guaranteed to be discarded.
  it("writes hard_gate_failures to the state file when a hard gate fails", async () => {
    const dir = await mkdtemp(join(tmpdir(), "psmith-p3-persist-"));
    try {
      await writeFile(join(dir, "paper.tex"), PAPER, "utf8");
      await writeFile(join(dir, "outline.md"), OUTLINE, "utf8");
      await writeFile(join(dir, "formal_layer.tex"), PAPER, "utf8");
      await writeFile(join(dir, "references.bib"), "", "utf8");
      await writeFile(
        join(dir, "formal_layer.json"),
        JSON.stringify({
          commit: "abc",
          blocks: [
            block("T-1", "theorem", "theoremv", "The rate depends on \\kappa."),
            block("P-1", "definition", "definitionv", "Let \\kappa be the exponent."),
          ],
        }),
        "utf8",
      );

      const state: PaperState = freshPaperState(QID, SPEC);
      const io = {
        ctx: {
          repoRoot: dir,
          qid: QID,
          spec: SPEC,
          deps: {
            dryRun: false,
            runClaude: async () => "{}",
            runCodex: async () => ({ stdout: "{}", stderr: "" }),
          },
        },
        state,
        bank: {} as never,
        outDir: dir,
      } as never;

      await expect(stageP3(io)).rejects.toThrow(/definition-order/);

      // The whole point of the field: it must survive the throw, on disk.
      const persisted = JSON.parse(
        await readFile(join(dir, `${QID}_${SPEC}_paper_state.json`), "utf8"),
      );
      expect(persisted.hard_gate_failures.length).toBeGreaterThan(0);
      expect(JSON.stringify(persisted.hard_gate_failures)).toContain("notation-defined-after-use");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});
