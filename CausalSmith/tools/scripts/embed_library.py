# tools/scripts/embed_library.py
#
# Embed the Causalean library declarations into vectors for the semantic retrieval tier.
#
# MULTI-VIEW (Phase 1 of the retrieval-v2 plan): each decl can be embedded under several
# complementary "views", stored in separate sidecars, and the tier scores a query by the
# MAX cosine over the available views (so a view only ever helps). Views:
#   nl   : humanized name + first doc paragraph        (the original signal; default paths)
#   stmt : the Lean statement (type structure)         → library_embeddings.stmt.{f32,meta.json}
#   nbr  : name + doc + dependency-graph NEIGHBOURHOOD  → library_embeddings.nbr.{f32,meta.json}
#          (humanized names of `refs` + reverse-refs — gives word-poor decls far more
#           surface vocabulary, directly attacking the vocabulary-mismatch "gap" stratum)
#
# Usage: python embed_library.py [--view nl|stmt|nbr]   (default nl)
# The `nl` view keeps the exact original paths/format for backward compatibility.
import os
os.environ.setdefault("HF_HUB_OFFLINE", "1")        # cluster is offline; load cached weights only
os.environ.setdefault("TRANSFORMERS_OFFLINE", "1")
import json, hashlib, re, sys, argparse
import numpy as np

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))  # tools/scripts -> repo root = Causalean pkg
INDEX = os.path.join(ROOT, "doc", "library_index.json")
MODEL = "BAAI/bge-large-en-v1.5"   # cached locally (1024-dim); offline-safe. bge needs CLS pooling (below).

MAX_NEIGHBORS = 16  # cap neighbourhood terms so the text stays within the model's context window


def paths(view):
    """(f32, meta) sidecar paths for a view. `nl` keeps the original unsuffixed paths."""
    suffix = "" if view == "nl" else f".{view}"
    return (os.path.join(ROOT, "doc", f"library_embeddings{suffix}.f32"),
            os.path.join(ROOT, "doc", f"library_embeddings{suffix}.meta.json"))


def humanize(name: str) -> str:
    tail = name.split(".")[-1]
    parts = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", tail).replace("_", " ")
    return parts.strip()


def first_para(doc):
    return (doc or "").split("\n\n")[0].strip()


def nl_text(e, _ctx):
    head = humanize(e["name"])
    body = first_para(e.get("doc")) or (e.get("statement") or "")
    return f"{head}. {body}".strip()


def stmt_text(e, _ctx):
    # Lean statement, whitespace-collapsed. Light name context helps the encoder anchor a
    # word-poor type. (Full conclusion/hypothesis normalization is a later enhancement.)
    stmt = re.sub(r"\s+", " ", (e.get("statement") or "")).strip()
    return f"{humanize(e['name'])}. {stmt}".strip(". ").strip() or humanize(e["name"])


def nbr_text(e, ctx):
    # name + doc + humanized names of dependency-graph neighbours (refs = what it is built on,
    # reverse-refs = what uses it). Distinct neighbour words give a terse decl the vocabulary a
    # gap-stratum query shares with it even when its own name/doc do not.
    rev = ctx["rev"]
    present = ctx["present"]
    head = humanize(e["name"])
    body = first_para(e.get("doc")) or ""
    refs = [r for r in (e.get("refs") or []) if r in present and r != e["name"]]
    revs = [r for r in rev.get(e["name"], []) if r != e["name"]]
    seen, neigh = set(), []
    for r in refs + revs:
        if r in seen:
            continue
        seen.add(r)
        neigh.append(humanize(r))
        if len(neigh) >= MAX_NEIGHBORS:
            break
    tail = (" Related: " + "; ".join(neigh)) if neigh else ""
    return f"{head}. {body}{tail}".strip()


BUILDERS = {"nl": nl_text, "stmt": stmt_text, "nbr": nbr_text}


def resolve_model_dir(model_id):
    """A repo-relative model dir (e.g. `doc/retrieval_model_ft`, as stored in the meta) is
    resolved against ROOT; an absolute path or HF name is returned as-is."""
    cand = model_id if os.path.isabs(model_id) else os.path.join(ROOT, model_id)
    return cand if os.path.isdir(cand) and os.path.exists(os.path.join(cand, "modules.json")) else model_id


def load_st_model(model_id):
    """A saved SentenceTransformer dir (e.g. the fine-tuned encoder) carries its own pooling
    config; a raw HF checkpoint (bge) needs CLS pooling set explicitly."""
    from sentence_transformers import SentenceTransformer, models
    resolved = resolve_model_dir(model_id)
    if os.path.isdir(resolved) and os.path.exists(os.path.join(resolved, "modules.json")):
        return SentenceTransformer(resolved)
    word = models.Transformer(resolved)
    pool = models.Pooling(word.get_word_embedding_dimension(), pooling_mode_cls_token=True, pooling_mode_mean_tokens=False)
    return SentenceTransformer(modules=[word, pool])


def default_model():
    """The model that built the current embeddings (so `embed:library` refreshes stay on the
    fine-tuned encoder); falls back to the base bge name when no embeddings exist yet."""
    try:
        return json.load(open(paths("nl")[1])).get("model") or MODEL
    except Exception:
        return MODEL


def build_context(ents):
    present = {e["name"] for e in ents}
    rev = {}
    for e in ents:
        for r in e.get("refs", []) or []:
            if r in present and r != e["name"]:
                rev.setdefault(r, []).append(e["name"])
    return {"present": present, "rev": rev}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--view", default="nl", choices=sorted(BUILDERS.keys()))
    ap.add_argument("--model-path", default=None, help="HF name or model dir (default: the model that built the current embeddings)")
    args = ap.parse_args()
    view = args.view
    model_id = args.model_path or default_model()
    F32, META = paths(view)
    builder = BUILDERS[view]

    lib = json.load(open(INDEX))
    ents = lib["entries"]
    ctx = build_context(ents)
    texts = {e["name"]: builder(e, ctx) for e in ents}
    hashes = {n: hashlib.sha1(t.encode()).hexdigest() for n, t in texts.items()}

    # content-hash cache: reuse unchanged rows (per view + model — hashes differ across views,
    # and a different encoder invalidates every row).
    cached = {}
    if os.path.exists(META) and os.path.exists(F32):
        old = json.load(open(META))
        if old.get("model") == model_id and old.get("view", "nl") == view:
            dim = old["dim"]
            buf = np.fromfile(F32, dtype=np.float32).reshape(-1, dim)
            for i, n in enumerate(old["names"]):
                if old["hashes"][i] == hashes.get(n):
                    cached[n] = buf[i]

    todo = [n for n in texts if n not in cached]
    print(f"[view={view}] {len(ents)} decls; reusing {len(cached)} cached, embedding {len(todo)}", file=sys.stderr)
    vecs = {}
    if todo:
        m = load_st_model(model_id)
        emb = m.encode([texts[n] for n in todo], normalize_embeddings=True,
                       batch_size=32, show_progress_bar=True)
        for n, v in zip(todo, emb):
            vecs[n] = np.asarray(v, dtype=np.float32)
    names = list(texts.keys())
    dim = (next(iter(cached.values())) if cached else vecs[todo[0]]).shape[0]
    mat = np.zeros((len(names), dim), dtype=np.float32)
    for i, n in enumerate(names):
        mat[i] = cached.get(n) if n in cached else vecs[n]
    mat.tofile(F32)
    json.dump({"model": model_id, "view": view, "dim": int(dim), "count": len(names),
               "index_commit": lib.get("commit"), "names": names,
               "hashes": [hashes[n] for n in names]}, open(META, "w"))
    print(f"[view={view}] wrote {F32} ({mat.nbytes} bytes) + {META}", file=sys.stderr)


if __name__ == "__main__":
    main()
