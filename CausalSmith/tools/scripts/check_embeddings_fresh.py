import json, hashlib, sys, os
from embed_library import BUILDERS, INDEX, paths, build_context  # reuse the exact per-view text logic

# Views produced by `npm run embed:library` (see package.json: `nl` default + `nbr`).
VIEWS = ["nl", "nbr"]


def check_view(view, ents, ctx):
    _f32, meta_path = paths(view)
    if not os.path.exists(meta_path):
        print(f"STALE [{view}]: no embeddings meta — run `npm run embed:library`", file=sys.stderr)
        return False
    builder = BUILDERS[view]
    cur = {e["name"]: hashlib.sha1(builder(e, ctx).encode()).hexdigest() for e in ents}
    meta = json.load(open(meta_path))
    old = dict(zip(meta["names"], meta["hashes"]))
    added = [n for n in cur if n not in old]
    removed = [n for n in old if n not in cur]
    changed = [n for n in cur if n in old and cur[n] != old[n]]
    if added or removed or changed:
        print(f"STALE embeddings [{view}]: +{len(added)} -{len(removed)} ~{len(changed)} vs meta "
              f"— run `npm run embed:library`", file=sys.stderr)
        for n in (added[:5] + removed[:5] + changed[:5]):
            print("  ", n, file=sys.stderr)
        return False
    print(f"embeddings fresh [{view}] ({len(cur)} decls)")
    return True


def main():
    ents = json.load(open(INDEX))["entries"]
    ctx = build_context(ents)
    results = [check_view(v, ents, ctx) for v in VIEWS]  # eager: report every view, not just the first stale one
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())
