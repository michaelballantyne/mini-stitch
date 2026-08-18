"""part_b.py --- is stitch's winning abstraction reachable by anti-unification?

For one corpus:
  1. run the real stitch binary (--max-arity=2 --iterations=1) and take the
     winning abstraction's body / arity / utility. The run is NOT --silent, so
     stitch's end-of-step `Stats { worklist_steps: N, ... }` debug line is on
     stdout; we scrape worklist_steps as the top-down search-space size
     (Part C of the experiment).
  2. compute the winner's match set over unique corpus subtrees, with
     de Bruijn-aware consistent-shifted-argument binding.
  3. check, modulo canonical variable renaming:
       SEED   -- winner == pairwise lgg of at least one pair of its matches
       CLOSED -- winner == lgg (fold of au) of its entire match set
     both are checked twice: over ALL matched locations, and over only the
     non-capturing ones (stitch zeroes the utility of capturing locations,
     so its effective match set is the non-capturing one).

Usage:
    python3 part_b.py CORPUS.json --name NAME [--out results_b.jsonl]
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time

from au_core import Arena, FusedTagError, load_corpus

BINARY = "/home/user/mini-stitch/stitch/target/release/compress"
SCRATCH = os.environ.get(
    "SCRATCH",
    "/tmp/claude-0/-home-user/5ddc7fad-43db-50ed-b98c-c1c3afbc8357/scratchpad")


def run_stitch(corpus_path, name):
    out = os.path.join(SCRATCH, "au-feas-%s-a2-i1.json" % name)
    proc = subprocess.run(
        [BINARY, corpus_path, "--max-arity=2", "--iterations=1",
         "--out=%s" % out],
        capture_output=True, text=True, timeout=600)
    if proc.returncode != 0:
        raise RuntimeError("stitch failed on %s: %s" % (name, proc.stderr[-500:]))
    m = re.search(r"worklist_steps: (\d+)", proc.stdout)
    worklist_steps = int(m.group(1)) if m else None
    with open(out) as f:
        result = json.load(f)
    return result, worklist_steps


def fold_lgg(a, locs):
    """Raw (kvar) lgg pattern of the whole set; canonicalize afterwards."""
    acc = locs[0]
    for t in locs[1:]:
        acc = a.au(acc, t)
    return acc


def freeze_ivars(a, p):
    """Replace each ivar #i in a canonical pattern by a fresh opaque primitive
    !vi, so the pattern can act as a concrete matching target."""

    def walk(idx):
        n = a.nodes[idx]
        k = n[0]
        if k == 'ivar':
            return a.add(('prim', '!v%d' % n[1]))
        if k == 'app':
            f = walk(n[1])
            x = walk(n[2])
            return a.add(('app', f, x))
        if k == 'lam':
            return a.add(('lam', walk(n[1])))
        return idx

    return walk(p)


def run(corpus_path, name):
    res = {"corpus": name, "path": corpus_path}
    programs = load_corpus(corpus_path)
    a = Arena()
    try:
        roots = [a.parse(p) for p in programs]
    except FusedTagError as e:
        res["skipped"] = "fused-lambda tags: %s" % e
        return res
    span = len(a.nodes)

    stitch_out, worklist_steps = run_stitch(corpus_path, name)
    res["worklist_steps"] = worklist_steps
    abstractions = stitch_out.get("abstractions", [])
    if not abstractions:
        res["no_abstraction"] = True
        return res
    winner = abstractions[0]
    res["winner_body"] = winner["body"]
    res["winner_arity"] = winner["arity"]
    res["winner_utility"] = winner["utility"]
    res["winner_num_uses"] = winner.get("num_uses")

    pat = a.parse(winner["body"])
    canon_winner = a.canonicalize_ivars(pat)

    # match set over unique corpus subtrees (span only)
    t0 = time.perf_counter()
    matches = []       # all matched unique subtrees
    noncap = []        # matched and no argument captures
    for t in range(span):
        r = a.match(pat, t)
        if r is not None:
            matches.append(t)
            if not r[1]:
                noncap.append(t)
    res["match_locations"] = len(matches)
    res["noncapturing_locations"] = len(noncap)

    # occurrence counts (num-paths): matches are unique subtrees, but each can
    # occur many times; the >=2 sanity check is about occurrences.
    counts = [0] * span
    for r in roots:
        counts[r] += 1
    for idx in range(span - 1, -1, -1):
        k = counts[idx]
        if k:
            n = a.nodes[idx]
            if n[0] == 'app':
                counts[n[1]] += k
                counts[n[2]] += k
            elif n[0] == 'lam':
                counts[n[1]] += k
    res["matched_occurrences"] = sum(counts[t] for t in matches)

    def seed_check(locs):
        """winner == pairwise lgg of some pair of locs (exactly, or after
        re-generalizing free de Bruijn vars)?"""
        n = len(locs)
        exact_pair = None
        fv_pair = None
        for i in range(n):
            for j in range(i + 1, n):
                raw = a.au(locs[i], locs[j])
                if a.canonicalize(raw) == canon_winner:
                    exact_pair = (locs[i], locs[j])
                    return exact_pair, exact_pair
                if fv_pair is None and \
                   a.canonicalize(a.regeneralize_free_vars(raw)) == canon_winner:
                    fv_pair = (locs[i], locs[j])
        return exact_pair, fv_pair

    checks = {}
    for label, locs in (("all", matches), ("noncap", noncap)):
        if len(locs) < 2:
            checks[label] = {"seed": None, "closed": None,
                             "note": "fewer than 2 locations"}
            continue
        exact_pair, fv_pair = seed_check(locs)
        raw_lgg = fold_lgg(a, locs)
        set_lgg = a.canonicalize(raw_lgg)
        set_lgg_fv = a.canonicalize(a.regeneralize_free_vars(raw_lgg))
        closed_ok = (set_lgg == canon_winner)
        closed_fv_ok = (set_lgg_fv == canon_winner)
        # Is the winner a generalization of the set-lgg (winner >= lgg in the
        # subsumption lattice)? If so, bottom-up AU reaches a pattern the
        # winner can be derived from by merging subpatterns into variables.
        # Test by freezing the lgg's variables into fresh opaque prims and
        # matching the winner against the frozen lgg tree.
        frozen = freeze_ivars(a, set_lgg)
        generalizes = a.match(pat, frozen) is not None
        entry = {"seed": exact_pair is not None,
                 "seed_fv": fv_pair is not None,
                 "closed": closed_ok,
                 "closed_fv": closed_fv_ok,
                 "winner_generalizes_set_lgg": generalizes}
        pair = exact_pair or fv_pair
        if pair:
            entry["seed_pair"] = [a.to_string(pair[0]), a.to_string(pair[1])]
        if not closed_ok:
            entry["set_lgg"] = a.to_string(set_lgg)
            if not closed_fv_ok:
                entry["set_lgg_fv"] = a.to_string(set_lgg_fv)
            entry["winner_canon"] = a.to_string(canon_winner)
        checks[label] = entry
    res["checks"] = checks
    res["check_seconds"] = round(time.perf_counter() - t0, 3)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("corpus")
    ap.add_argument("--name", required=True)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(
        os.path.abspath(__file__)), "results_b.jsonl"))
    args = ap.parse_args()
    res = run(args.corpus, args.name)
    with open(args.out, "a") as f:
        f.write(json.dumps(res) + "\n")
    print(json.dumps(res, indent=2))


if __name__ == "__main__":
    main()
