# tools/scripts/build_finetune_data.py
#
# Phase 2 (retrieval-v2): build contrastive training pairs for fine-tuning the bge bi-encoder
# on the Causalean library, with a MODULE-LEVEL train/test split so the fine-tuned encoder is
# evaluated only on modules it never trained on (the refs graph is both a training signal AND
# the eval gold, so a random per-theorem split would leak through shared neighbourhoods).
#
# Positives (offline, no LLM — derived from the index itself):
#   doc2ref  : (docstring-first-para of theorem T, nl-text of each core ref of T)
#              — mirrors the eval task "NL description -> the decls it is built on".
#   stmt2doc : (Lean statement of decl D, docstring of D) — cross-view NL<->Lean alignment.
#
# All positives come from TRAIN-module decls only. The held-out TEST module list is written so
# the eval can restrict to it for a leak-free number (retrieval_eval --test-modules).
#
# Usage: python build_finetune_data.py --out <dir> [--test-frac 0.15] [--idf-floor 2.3]
import os, json, re, hashlib, argparse, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
INDEX = os.path.join(ROOT, "doc", "library_index.json")

GOLD_KINDS = {"def", "structure", "inductive", "class", "abbrev", "theorem"}


def humanize(name):
    tail = name.split(".")[-1]
    return re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", tail).replace("_", " ").strip()


def first_para(doc):
    return (doc or "").split("\n\n")[0].strip()


def nl_text(e):
    body = first_para(e.get("doc")) or (e.get("statement") or "")
    return f"{humanize(e['name'])}. {body}".strip()


def module_of(e):
    return e.get("module") or e.get("file") or ""


def is_test_module(mod, test_frac):
    # Deterministic hash split on the module name — stable across runs, no RNG.
    h = int(hashlib.sha1(mod.encode()).hexdigest()[:8], 16) / 0xFFFFFFFF
    return h < test_frac


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--test-frac", type=float, default=0.15)
    ap.add_argument("--idf-floor", type=float, default=2.3)
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)

    lib = json.load(open(INDEX))
    ents = lib["entries"]
    by_name = {e["name"]: e for e in ents}

    # document-frequency IDF over theorem refs → drop ubiquitous carrier decls (same as eval).
    import math
    df = {}
    thms = [e for e in ents if e.get("kind") == "theorem"]
    for T in thms:
        gold = set()
        for r in T.get("refs", []) or []:
            ref = by_name.get(r)
            if ref and r != T["name"] and not T["name"].startswith(r + ".") and ref.get("kind") in GOLD_KINDS:
                gold.add(r)
        for g in gold:
            df[g] = df.get(g, 0) + 1
    N = len(thms)
    idf = {g: math.log((N + 1) / (c + 1)) for g, c in df.items()}

    def core_refs(T):
        out = []
        for r in T.get("refs", []) or []:
            ref = by_name.get(r)
            if not ref or r == T["name"] or T["name"].startswith(r + ".") or ref.get("kind") not in GOLD_KINDS:
                continue
            if idf.get(r, 1e9) >= args.idf_floor:
                out.append(r)
        return out

    test_modules = sorted({module_of(e) for e in ents if is_test_module(module_of(e), args.test_frac)})
    test_set = set(test_modules)

    pairs = []
    n_doc2ref = n_stmt2doc = 0
    for T in thms:
        if module_of(T) in test_set:
            continue  # train pairs from train modules only
        doc = first_para(T.get("doc"))
        if doc:
            for r in core_refs(T):
                pairs.append({"a": doc, "b": nl_text(by_name[r]), "kind": "doc2ref"})
                n_doc2ref += 1
    for e in ents:
        if module_of(e) in test_set:
            continue
        doc = first_para(e.get("doc"))
        stmt = re.sub(r"\s+", " ", (e.get("statement") or "")).strip()
        if doc and stmt:
            pairs.append({"a": f"{humanize(e['name'])}. {stmt}", "b": f"{humanize(e['name'])}. {doc}", "kind": "stmt2doc"})
            n_stmt2doc += 1

    with open(os.path.join(args.out, "train_pairs.jsonl"), "w") as f:
        for p in pairs:
            f.write(json.dumps(p) + "\n")
    json.dump(test_modules, open(os.path.join(args.out, "test_modules.json"), "w"))
    all_modules = sorted({module_of(e) for e in ents})
    stats = {
        "index_commit": lib.get("commit"), "n_entries": len(ents), "n_theorems": N,
        "n_modules": len(all_modules), "n_test_modules": len(test_modules),
        "n_pairs": len(pairs), "n_doc2ref": n_doc2ref, "n_stmt2doc": n_stmt2doc,
        "test_frac": args.test_frac, "idf_floor": args.idf_floor,
    }
    json.dump(stats, open(os.path.join(args.out, "split_stats.json"), "w"), indent=2)
    print(json.dumps(stats, indent=2), file=sys.stderr)


if __name__ == "__main__":
    main()
