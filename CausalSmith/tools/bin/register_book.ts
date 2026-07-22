#!/usr/bin/env -S npx tsx
/**
 * Interactive textbook / lecture-notes registration helper for the retired study pipeline.
 *
 *   register_book.ts --pdf <path> [--kind textbook|lecture_notes] [--book-id <id>]
 *
 * Prompts for title / authors / year / isbn? / edition? / chapter_index?;
 * copies the PDF into `doc/study/<textbooks|lecture_notes>/<book_id>/source.pdf`;
 * writes `meta.json`; prints the canonical ref string suitable for
 * `--learn ... --source <ref>` (retired study CLI).
 *
 * Resolver counterpart: `tools/src/shared/resolve_source.ts`.
 */
import { existsSync, readFileSync } from "node:fs";
import { copyFile, mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import * as readline from "node:readline/promises";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";


function parseArgs(argv: string[]): {
  pdf: string;
  kind: "textbook" | "lecture_notes";
  bookId?: string;
} {
  let pdf: string | undefined;
  let kind: "textbook" | "lecture_notes" = "textbook";
  let bookId: string | undefined;
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--pdf") pdf = argv[++i];
    else if (a === "--kind") {
      const k = argv[++i];
      if (k !== "textbook" && k !== "lecture_notes") {
        throw new Error(`--kind must be textbook|lecture_notes; got ${k}`);
      }
      kind = k;
    } else if (a === "--book-id") {
      bookId = argv[++i];
    }
  }
  if (!pdf) throw new Error("Usage: register_book.ts --pdf <path> [--kind textbook|lecture_notes] [--book-id <id>]");
  return { pdf, kind, bookId };
}

function slugify(s: string): string {
  return s
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "-")
    .replace(/^-+|-+$/g, "")
    .slice(0, 60);
}

async function uniqueBookId(root: string, base: string): Promise<string> {
  if (!existsSync(path.join(root, base))) return base;
  for (const suffix of ["a", "b", "c", "d", "e", "f", "g", "h"]) {
    const cand = `${base}${suffix}`;
    if (!existsSync(path.join(root, cand))) return cand;
  }
  throw new Error(`Cannot mint a unique book_id from base "${base}" (a-h all taken)`);
}

async function main() {
  const args = parseArgs(process.argv.slice(2));
  const repoRoot = findCausalSmithRoot(process.cwd());
  const studyRoot = path.join(repoRoot, "doc", "study");
  const targetParent = path.join(studyRoot, args.kind === "textbook" ? "textbooks" : "lecture_notes");

  if (!existsSync(args.pdf)) throw new Error(`PDF not found: ${args.pdf}`);

  const rl = readline.createInterface({ input: process.stdin, output: process.stdout });
  try {
    const title = (await rl.question("Title: ")).trim();
    const authorsRaw = (await rl.question("Authors (comma-separated): ")).trim();
    const yearRaw = (await rl.question("Year: ")).trim();
    const isbn = (await rl.question("ISBN (optional): ")).trim() || undefined;
    const edition = (await rl.question("Edition (optional): ")).trim() || undefined;
    const chapterIndex = (await rl.question("Chapter index (optional, free-form): ")).trim() || undefined;

    const authors = authorsRaw
      .split(",")
      .map((s) => s.trim())
      .filter(Boolean);
    if (authors.length === 0) throw new Error("At least one author required.");

    const year = Number(yearRaw);
    if (!Number.isFinite(year)) throw new Error(`Invalid year: ${yearRaw}`);

    const baseId = args.bookId ?? slugify(`${authors[0].split(/\s+/).pop() ?? authors[0]}${year}`);
    const bookId = await uniqueBookId(targetParent, baseId);

    const dest = path.join(targetParent, bookId);
    await mkdir(dest, { recursive: true });
    const destPdf = path.join(dest, "source.pdf");
    if (existsSync(destPdf)) {
      throw new Error(`Refusing to overwrite ${destPdf}`);
    }
    await copyFile(args.pdf, destPdf);

    const meta = {
      schema_version: 1,
      book_id: bookId,
      kind: args.kind,
      title,
      authors,
      year,
      ...(isbn !== undefined ? { isbn } : {}),
      ...(edition !== undefined ? { edition } : {}),
      ...(chapterIndex !== undefined ? { chapter_index: chapterIndex } : {}),
      registered_at: new Date().toISOString(),
    };
    await writeFile(path.join(dest, "meta.json"), `${JSON.stringify(meta, null, 2)}\n`, "utf8");

    console.log(`Registered ${bookId} at ${dest}`);
    console.log(`Use ref: ${bookId}:chN  (replace N with the chapter you want to study; range form: ${bookId}:ch3-5)`);
  } finally {
    rl.close();
  }
}

main().catch((err: unknown) => {
  const msg = err instanceof Error ? err.message : String(err);
  console.error(`register_book: ${msg}`);
  process.exitCode = 1;
});
