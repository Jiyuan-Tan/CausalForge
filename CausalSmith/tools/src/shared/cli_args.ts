// Shared argv reading for the `bin/` entry points.
//
// WHY THIS EXISTS. 40 entry points each re-implemented their own parsing: five
// distinct `flag()` bodies, a `flags()`, an `argVal()`, seven copies of the
// positional filter, and eight copies of the `"-" -> read stdin` idiom. Two of the
// `flag()` variants differ in CALLING CONVENTION — `flag(args, "--out")` vs
// `flag(args, "out")` (which prepends the dashes itself) — so copy-pasting a call
// between two files silently reads the wrong flag.
//
// None of them guarded the VALUE. `indexOf(name) + 1` returns whatever token comes
// next, so `--directive --require-core-changes` sets the directive to the literal
// string "--require-core-changes" and the real boolean flag is consumed. That is a
// silent wrong-input bug in operator tooling, which is exactly where it is least
// likely to be noticed.
//
// One convention here: flag names always include their leading dashes, and a value
// that looks like another flag is refused rather than swallowed.

import { readFileSync } from "node:fs";

/** Thrown when argv is malformed in a way that would otherwise be read as data. */
export class CliArgsError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "CliArgsError";
  }
}

function looksLikeFlag(token: string | undefined): boolean {
  return token !== undefined && token.startsWith("--");
}

export interface ReadArgsOptions {
  /** Flags whose value may legitimately begin with `--`. */
  allowFlagLikeValues?: readonly string[];
}

export class ArgReader {
  readonly argv: readonly string[];
  private readonly allowFlagLike: ReadonlySet<string>;

  constructor(argv: readonly string[], opts: ReadArgsOptions = {}) {
    this.argv = argv;
    this.allowFlagLike = new Set(opts.allowFlagLikeValues ?? []);
  }

  /** First value for `name` (which MUST include its leading `--`), or undefined.
   *  Refuses a value that looks like another flag — that is a malformed invocation,
   *  not a value. */
  value(name: string): string | undefined {
    const i = this.argv.indexOf(name);
    if (i === -1) return undefined;
    const v = this.argv[i + 1];
    if (v === undefined) {
      throw new CliArgsError(`${name} requires a value but was given none.`);
    }
    if (looksLikeFlag(v) && !this.allowFlagLike.has(name)) {
      throw new CliArgsError(
        `${name} was followed by '${v}', which looks like another flag rather than a value. ` +
          `Quote the value if it genuinely starts with '--'.`,
      );
    }
    return v;
  }

  /** Every value for a repeatable flag, in argv order. */
  values(name: string): string[] {
    const out: string[] = [];
    for (let i = 0; i < this.argv.length; i += 1) {
      if (this.argv[i] !== name) continue;
      const v = this.argv[i + 1];
      if (v === undefined || (looksLikeFlag(v) && !this.allowFlagLike.has(name))) continue;
      out.push(v);
    }
    return out;
  }

  /** Presence of a boolean flag. */
  bool(name: string): boolean {
    return this.argv.includes(name);
  }

  /** Positional arguments — tokens that are neither a flag nor a flag's value. */
  positionals(): string[] {
    const out: string[] = [];
    for (let i = 0; i < this.argv.length; i += 1) {
      const tok = this.argv[i];
      if (looksLikeFlag(tok)) {
        // Skip this flag's value too, unless the next token is itself a flag
        // (i.e. this one is boolean).
        if (!looksLikeFlag(this.argv[i + 1]) && this.argv[i + 1] !== undefined) i += 1;
        continue;
      }
      out.push(tok);
    }
    return out;
  }

  /** Resolve the conventional `-` sentinel to stdin. Returns the value unchanged
   *  otherwise, and undefined when the flag was absent. */
  valueOrStdin(name: string): string | undefined {
    const v = this.value(name);
    if (v === undefined) return undefined;
    return v === "-" ? readFileSync(0, "utf8") : v;
  }
}

/** Read `process.argv` (minus node + script) with the shared conventions. */
export function readArgs(
  argv: readonly string[] = process.argv.slice(2),
  opts: ReadArgsOptions = {},
): ArgReader {
  return new ArgReader(argv, opts);
}
