# tools/scripts/mine_anchor_candidates.py
#
# Phase 5 (retrieval-v2): mine BEHAVIORALLY-VERIFIED (concept -> Causalean decl) candidate rows for
# the retrieval-eval anchor set, from accepted causalsmith research runs. The anchor is the leak-free release
# gate; its rows must be real-consumer prose (F1-item concept text) paired with a decl the agent
# actually USED in a proof that LANDED — not merely proposed.
#
# The robust signal is the INTERSECTION (per the data map): a Causalean decl NAMED against an F1
# item's obj_id in graph.json (node.lean.decl_name, or a Causalean.* mention in node.nl.statement)
# AND actually referenced (import or FQ body usage) in the type-checking landed Lean proof. A decl
# proposed-but-flagged in the log, or used-but-untied-to-any-item, is dropped.
#
# Output: a CANDIDATES review file (JSONL) — item text + gold decl + cluster + evidence — for HAND
# verification before anything is appended to anchor.jsonl. This script never edits the anchor.
#
# Usage: python3 mine_anchor_candidates.py --out <candidates.jsonl>
import os, json, re, argparse, glob, sys

CS = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))          # CausalSmith pkg root
REPO = os.path.abspath(os.path.join(CS, ".."))                                     # workspace root
ACCEPTED = os.path.join(CS, "doc", "research", "_bank", "accepted")

# Library-proper Causalean namespaces we treat as concept-level gold (Mathlib-ext helpers excluded —
# they are plumbing, not a concept a downstream agent searches for).
LIB_PROPER = ("Causalean.Stat.", "Causalean.Experimentation.", "Causalean.Estimation.",
              "Causalean.PO.", "Causalean.ExactID.", "Causalean.PartialID.", "Causalean.SCM.",
              "Causalean.Panel.", "Causalean.Identification.")
CLUSTER_BY_PREFIX = {"stat": "stat", "exp": "experimentation", "eid": "exactid",
                     "pid": "partialid", "q1": "panel", "scm": "scm"}
FQN = re.compile(r"Causalean(?:\.[A-Za-z_][A-Za-z0-9_']*)+")


def is_lib_proper(name):
    return name.startswith(LIB_PROPER)


def cluster_of(state):
    sub = (state.get("lean_subdir") or "").lower()
    for key, cl in (("/stat/", "stat"), ("/experimentation/", "experimentation"), ("/exactid/", "exactid"),
                    ("/partialid/", "partialid"), ("/panel/", "panel"), ("/scm/", "scm")):
        if key in sub:
            return cl
    qid = (state.get("qid") or "")
    return CLUSTER_BY_PREFIX.get(qid.split("_")[0], None)


def landed_usage(lean_dir):
    """Ground-truth Causalean.* names referenced (import + body) across the landed proof tree,
    with a coarse usage count. Only library-proper names are kept."""
    counts = {}
    for path in glob.glob(os.path.join(lean_dir, "**", "*.lean"), recursive=True):
        try:
            txt = open(path, encoding="utf-8").read()
        except OSError:
            continue
        for m in FQN.findall(txt):
            if is_lib_proper(m):
                counts[m] = counts.get(m, 0) + 1
    return counts


def item_text(nl):
    """The F1-item concept prose: the clause BEFORE the Stage-2 '— <verdict>' the survey appends."""
    s = re.sub(r"\s+", " ", (nl or "")).strip()
    return s.split(" — ")[0].split(" -- ")[0].strip()


def nodes_of(graph):
    if isinstance(graph, dict):
        return graph.get("nodes") or []
    return graph if isinstance(graph, list) else []


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    rows = []
    for run in sorted(glob.glob(os.path.join(ACCEPTED, "*"))):
        gpath, spath = os.path.join(run, "graph.json"), os.path.join(run, "state.json")
        if not (os.path.exists(gpath) and os.path.exists(spath)):
            continue
        state = json.load(open(spath))
        # lean_subdir (e.g. "CausalSmith/Stat/…") is relative to the CausalSmith PACKAGE root,
        # whose Lean tree is CausalSmith/CausalSmith/… — so join against CS, not the workspace.
        lean_dir = os.path.join(CS, state.get("lean_subdir", ""))
        if not os.path.isdir(lean_dir):
            continue
        used = landed_usage(lean_dir)                 # decl -> usage count (ground truth)
        cluster = cluster_of(state)
        qid = state.get("qid", os.path.basename(run))
        for n in nodes_of(json.load(open(gpath))):
            nl = (n.get("nl") or {}).get("statement", "")
            named = set()
            dn = (n.get("lean") or {}).get("decl_name")
            if isinstance(dn, str) and is_lib_proper(dn):
                named.add(dn)
            for m in FQN.findall(nl):                  # Causalean.* mentioned in this item's prose
                if is_lib_proper(m):
                    named.add(m)
            # INTERSECTION: named against THIS item AND behaviorally used in the landed proof.
            for decl in sorted(named & set(used)):
                rows.append({
                    "run": qid, "obj_id": n.get("obj_id"), "kind": n.get("kind"),
                    "cluster": cluster, "item": item_text(nl), "gold": [decl],
                    "evidence": {"landed_usage_count": used[decl],
                                 "via": "lean.decl_name" if decl == dn else "nl-mention"},
                })

    # dedup identical (item, gold)
    seen, uniq = set(), []
    for r in rows:
        key = (r["item"], r["gold"][0])
        if key in seen:
            continue
        seen.add(key)
        uniq.append(r)

    with open(args.out, "w") as f:
        for r in uniq:
            f.write(json.dumps(r) + "\n")
    print(f"{len(uniq)} candidate rows across accepted runs -> {args.out}", file=sys.stderr)
    from collections import Counter
    print("by cluster:", dict(Counter(r["cluster"] for r in uniq)), file=sys.stderr)
    print("by run:", dict(Counter(r["run"] for r in uniq)), file=sys.stderr)


if __name__ == "__main__":
    main()
