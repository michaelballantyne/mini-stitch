"""part_a.py --- corpus stats + the pairwise anti-unification space.

For one corpus: parse into a hash-consed arena, then compute the Plotkin lgg
of every unordered pair of distinct unique subtrees whose top constructors
are compatible (app/app or lam/lam; every other pair anti-unifies to a bare
variable and is counted as trivial). Reports distinct canonical patterns,
the number of distinct memoized au subproblems (the analogue of a datalog
join's intermediate relation), and wall time.

Usage:
    python3 part_a.py CORPUS.json --name NAME [--prefix N] [--budget SECONDS]
                      [--out results_a.jsonl]

Appends one JSON object per run to the --out file (default results_a.jsonl
next to this script). A run that exceeds --budget stops cleanly and records
partial progress with "timed_out": true.
"""

import argparse
import json
import os
import time

from au_core import Arena, FusedTagError, load_corpus


def run(corpus_path, name, prefix, budget):
    programs = load_corpus(corpus_path, prefix)
    res = {
        "corpus": name,
        "path": corpus_path,
        "prefix": prefix,
        "n_programs": len(programs),
    }

    a = Arena()
    try:
        t0 = time.perf_counter()
        roots = [a.parse(p) for p in programs]
        parse_s = time.perf_counter() - t0
    except FusedTagError as e:
        res["skipped"] = "fused-lambda tags: %s" % e
        return res

    span = len(a.nodes)
    res["total_tree_nodes"] = sum(a.tree_size(r) for r in roots)
    res["unique_subtrees"] = span
    res["parse_seconds"] = round(parse_s, 4)

    # group span subtrees by top constructor
    apps = [i for i in range(span) if a.nodes[i][0] == 'app']
    lams = [i for i in range(span) if a.nodes[i][0] == 'lam']
    n_apps, n_lams = len(apps), len(lams)
    res["n_app_subtrees"] = n_apps
    res["n_lam_subtrees"] = n_lams

    total_pairs = span * (span - 1) // 2
    compat_pairs = n_apps * (n_apps - 1) // 2 + n_lams * (n_lams - 1) // 2
    res["total_pairs"] = total_pairs
    res["compatible_pairs"] = compat_pairs
    res["trivial_pairs"] = total_pairs - compat_pairs  # lgg = bare variable

    distinct = set()          # canonical pattern ids
    au = a.au
    canon = a.canonicalize
    deadline = time.monotonic() + budget if budget else None
    done = 0
    t0 = time.perf_counter()
    timed_out = False
    for group in (apps, lams):
        n = len(group)
        for i in range(n):
            gi = group[i]
            for j in range(i + 1, n):
                distinct.add(canon(au(gi, group[j])))
            done += n - i - 1
            if deadline is not None and time.monotonic() > deadline:
                timed_out = True
                break
        if timed_out:
            break
    au_seconds = time.perf_counter() - t0

    res["pairs_done"] = done
    res["timed_out"] = timed_out
    res["distinct_lgg_patterns"] = len(distinct)
    # breakdown of the distinct canonical patterns
    with_var = 0
    with_repeated_var = 0
    max_vars = 0
    for p in distinct:
        nvars, occ = a.pattern_stats(p)
        if nvars > 0:
            with_var += 1
        if occ > nvars:
            with_repeated_var += 1
        if nvars > max_vars:
            max_vars = nvars
    res["distinct_with_ge1_var"] = with_var
    res["distinct_with_repeated_var"] = with_repeated_var
    res["max_vars_in_a_pattern"] = max_vars
    # "product size": distinct memoized au subproblems + one root call per pair
    res["au_root_calls"] = a.au_root_calls
    res["au_memo_entries"] = a.au_memo_size()
    res["au_subproblems_total"] = a.au_root_calls + a.au_memo_size()
    res["arena_size_after"] = len(a.nodes)
    res["au_seconds"] = round(au_seconds, 3)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("corpus")
    ap.add_argument("--name", required=True)
    ap.add_argument("--prefix", type=int, default=None)
    ap.add_argument("--budget", type=float, default=None,
                    help="soft time budget in seconds for the pair loop")
    ap.add_argument("--out", default=os.path.join(os.path.dirname(
        os.path.abspath(__file__)), "results_a.jsonl"))
    args = ap.parse_args()

    res = run(args.corpus, args.name, args.prefix, args.budget)
    with open(args.out, "a") as f:
        f.write(json.dumps(res) + "\n")
    print(json.dumps(res, indent=2))


if __name__ == "__main__":
    main()
