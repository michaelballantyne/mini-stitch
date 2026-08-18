"""gen_tables.py --- render the markdown tables in results.md from
results_a.jsonl / results_b.jsonl. Run: python3 gen_tables.py"""

import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))


def rows(path):
    with open(os.path.join(HERE, path)) as f:
        return [json.loads(l) for l in f]


def part_a():
    print("| corpus | prefix | progs | tree nodes | unique subtrees S | "
          "compatible pairs | trivial pairs | distinct lggs | w/ repeated var "
          "| max vars | au subproblems | au wall (s) |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|")
    for r in rows("results_a.jsonl"):
        if "skipped" in r:
            print("| %s | - | %d | (skipped: fused-lambda tags) |  |  |  |  |  |  |  |  |"
                  % (r["corpus"], r["n_programs"]))
            continue
        pfx = r["prefix"] if r["prefix"] else "full"
        to = " (TIMED OUT: %d pairs done)" % r["pairs_done"] if r["timed_out"] else ""
        print("| %s | %s | %d | %d | %d | %d | %d | %d%s | %d | %d | %d | %.3f |"
              % (r["corpus"], pfx, r["n_programs"], r["total_tree_nodes"],
                 r["unique_subtrees"], r["compatible_pairs"],
                 r["trivial_pairs"], r["distinct_lgg_patterns"], to,
                 r["distinct_with_repeated_var"], r["max_vars_in_a_pattern"],
                 r["au_subproblems_total"], r["au_seconds"]))


def v(x):
    return {True: "yes", False: "no", None: "-"}[x]


def part_b():
    print("| corpus | winner body (a2 i1) | arity | utility | uniq matches | "
          "occurrences | SEED | SEED+fv | CLOSED | CLOSED+fv | winner ⊇ set-lgg | "
          "worklist steps |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|")
    for r in rows("results_b.jsonl"):
        n = r["corpus"]
        if "skipped" in r:
            print("| %s | (skipped: fused-lambda tags) |  |  |  |  |  |  |  |  |  |  |" % n)
            continue
        if r.get("no_abstraction"):
            print("| %s | (no compressive abstraction) |  |  |  |  |  |  |  |  |  | %d |"
                  % (n, r["worklist_steps"]))
            continue
        e = r["checks"]["all"]
        body = "`%s`" % r["winner_body"]
        if len(r["winner_body"]) > 60:
            body = "`%s...`" % r["winner_body"][:57]
        print("| %s | %s | %d | %d | %d | %d | %s | %s | %s | %s | %s | %d |"
              % (n, body, r["winner_arity"], r["winner_utility"],
                 r["match_locations"], r["matched_occurrences"],
                 v(e.get("seed")), v(e.get("seed_fv")), v(e.get("closed")),
                 v(e.get("closed_fv")),
                 v(e.get("winner_generalizes_set_lgg")),
                 r["worklist_steps"]))


def part_c():
    a_by = {}
    for r in rows("results_a.jsonl"):
        if "skipped" not in r and not r["prefix"]:
            a_by[r["corpus"]] = r
    print("| corpus | top-down worklist steps (with pruning) | bottom-up "
          "compatible pairs (no pruning) | distinct pairwise lggs | ratio "
          "pairs/steps |")
    print("|---|---|---|---|---|")
    for r in rows("results_b.jsonl"):
        n = r["corpus"]
        if n not in a_by or r.get("worklist_steps") is None:
            continue
        a = a_by[n]
        ratio = a["compatible_pairs"] / max(r["worklist_steps"], 1)
        print("| %s | %d | %d | %d | %.1fx |"
              % (n, r["worklist_steps"], a["compatible_pairs"],
                 a["distinct_lgg_patterns"], ratio))


if __name__ == "__main__":
    print("### Part A\n")
    part_a()
    print("\n### Part B\n")
    part_b()
    print("\n### Part C\n")
    part_c()
