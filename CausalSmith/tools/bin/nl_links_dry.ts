#!/usr/bin/env -S npx tsx
/**
 * Go/no-go check before running the P4 NL↔Lean crosslink sub-step on a bundle.
 *
 * Runs every FREE pass of the sub-step — selection, block extraction, Lean
 * pieces and their reference closure, both prompt renderings, the cache read
 * side, the artifact read side — against real bundle data, with a runCodex that
 * throws if anything tries to spend a call. Exits nonzero on any error or
 * extraction failure, so an operator learns about a bundle shape the sub-step
 * cannot handle BEFORE paying for a run rather than halfway through one.
 *
 * Usage:
 *   nl_links_dry.ts <bundle-dir> [<bundle-dir> ...]
 *   nl_links_dry.ts --all [--root <dir>]     # every bundle with a meta.json
 */
import process from "node:process";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { dryRunBundle, findBundles, type BundleReport } from "../src/presentation/nl_links_dry.js";

const TOOLS_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const DEFAULT_ROOT = path.join(TOOLS_ROOT, "..", "doc", "presentation");

function row(r: BundleReport): string {
  const cells = [
    r.ok ? "ok  " : "FAIL",
    r.bundle.slice(0, 44).padEnd(44),
    String(r.blocks).padStart(4),
    String(r.extractionFailures.length).padStart(4),
    String(r.unstructured.length).padStart(6),
    `${r.rows.min}/${r.rows.median}/${r.rows.max}`.padStart(10),
    `${r.segments.min}/${r.segments.median}/${r.segments.max}`.padStart(10),
    String(r.segments.displays).padStart(5),
    String(r.assignChunks).padStart(6),
    String(r.verifyChunks).padStart(6),
    `${Math.round(r.promptBytesMax / 1024)}k`.padStart(7),
  ];
  return cells.join(" ");
}

async function main(): Promise<void> {
  const argv = process.argv.slice(2);
  const rootAt = argv.indexOf("--root");
  const root = rootAt >= 0 ? argv[rootAt + 1] : DEFAULT_ROOT;
  const dirs = argv.includes("--all")
    ? await findBundles(root)
    : argv.filter((a) => !a.startsWith("--") && a !== root);
  if (dirs.length === 0) {
    throw new Error(`nl_links_dry: no bundle directories (looked under ${root}); pass a dir or --all`);
  }
  const reports: BundleReport[] = [];
  for (const dir of dirs) reports.push(await dryRunBundle(dir));

  console.log(
    ["stat", "bundle".padEnd(44), "blks", "xfai", "unstr", "rows m/m/M", "segs m/m/M", "disp", "assign", "verify", "maxB"].join(" "),
  );
  for (const r of reports) console.log(row(r));

  for (const r of reports) {
    const notes = [
      `caches: assign ${r.caches.assign}; verify ${r.caches.verify}`,
      `artifact: ${r.artifact}`,
      `rows ${r.rows.total}, segments ${r.segments.total} (${r.segments.displays} displays)`,
      `skipped: ${r.skipped.webOnly} web-only, ${r.skipped.synthesized} synthesized, ` +
        `${r.skipped.noSnippet} no-snippet, ${r.skipped.noLean} no-lean-text, ${r.skipped.noBlock} no-body-block`,
      ...(r.unstructured.length > 0
        ? [`unstructured (segments only, site falls back): ${r.unstructured.slice(0, 6).join(", ")}`]
        : []),
      ...r.extractionFailures.map((id) => `EXTRACTION FAILURE: ${id}`),
      ...r.anomalies.map((a) => `anomaly: ${a}`),
      ...r.errors.map((e) => `ERROR: ${e}`),
    ];
    console.log(`\n${r.bundle}\n  ${notes.join("\n  ")}`);
  }

  const bad = reports.filter((r) => !r.ok);
  console.log(
    `\nnl_links_dry: ${reports.length - bad.length}/${reports.length} bundles ready` +
      (bad.length > 0 ? ` — NOT READY: ${bad.map((b) => b.bundle).join(", ")}` : ""),
  );
  if (bad.length > 0) process.exitCode = 1;
}

main().catch((error) => {
  console.error(error instanceof Error ? error.message : error);
  process.exitCode = 1;
});
