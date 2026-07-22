// Framework primitive 1 of 3: the ONLY way ported D-stage code touches a JSON
// store on disk. Loud missing-file semantics (no existsSync-fail-open), Zod at
// the boundary, atomic writes. See docs/superpowers/specs/2026-07-20-dstage-
// framework-rewrite-design.md §Stores.
import { existsSync } from "node:fs";
import { mkdir, readFile } from "node:fs/promises";
import path from "node:path";
import type { ZodType } from "zod";
import { writeJsonAtomic } from "../../shared/json_atomic.js";
import type { PipelineContext } from "../../types.js";

export interface StoreDef<T> {
  /** Stable registry id, e.g. "proto_core". Used in every error message. */
  id: string;
  /** Resolve the on-disk path. Canonical-vs-legacy resolution lives HERE, nowhere else. */
  resolve: (ctx: PipelineContext) => string;
  schema: ZodType<T>;
}

export interface Store<T> {
  id: string;
  path(ctx: PipelineContext): string;
  /** Loud load: throws with the resolved path when missing, corrupt, or schema-invalid. */
  load(ctx: PipelineContext): Promise<T>;
  /** Explicit absence: null when the file does not exist. Corruption still throws —
   *  a corrupt store must never read as "empty" (that adjudicates a phantom state). */
  loadOptional(ctx: PipelineContext): Promise<T | null>;
  /** Validate → mkdir → atomic write. Rejects an invalid value before touching disk. */
  save(ctx: PipelineContext, value: T): Promise<void>;
}

export function defineJsonStore<T>(def: StoreDef<T>): Store<T> {
  const parse = (raw: string, p: string): T => {
    let parsed: unknown;
    try {
      parsed = JSON.parse(raw);
    } catch (err) {
      throw new Error(
        `store '${def.id}' at ${p} is not valid JSON: ${err instanceof Error ? err.message : String(err)}`,
      );
    }
    const result = def.schema.safeParse(parsed);
    if (!result.success) {
      throw new Error(`store '${def.id}' at ${p} failed schema validation: ${result.error.message}`);
    }
    return result.data;
  };
  return {
    id: def.id,
    path: (ctx) => def.resolve(ctx),
    async load(ctx) {
      const p = def.resolve(ctx);
      if (!existsSync(p)) {
        throw new Error(
          `store '${def.id}' is missing at ${p} (required by this stage — a missing store is a fault, not an empty state)`,
        );
      }
      return parse(await readFile(p, "utf8"), p);
    },
    async loadOptional(ctx) {
      const p = def.resolve(ctx);
      if (!existsSync(p)) return null;
      return parse(await readFile(p, "utf8"), p);
    },
    async save(ctx, value) {
      const result = def.schema.safeParse(value);
      if (!result.success) {
        throw new Error(`store '${def.id}' refused to save a schema-invalid value: ${result.error.message}`);
      }
      const p = def.resolve(ctx);
      await mkdir(path.dirname(p), { recursive: true });
      await writeJsonAtomic(p, result.data);
    },
  };
}
