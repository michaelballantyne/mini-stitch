"""run_large.py --- drive the large-corpora extension of the AU feasibility
experiment (see results-large.md). Two subcommands, each appending one JSON
record to results_large.jsonl so partial progress survives:

  python3 run_large.py au CORPUS.json --name NAME [--prefix N] [--budget S]
      Part-A-style pairwise-AU measurement (reuses part_a.run unchanged).

  python3 run_large.py stitch CORPUS.json --name NAME [--arity 2]
      [--fmt programs-list|dreamcoder] [--timeout 600]
      Real stitch binary at --iterations=1; records wall time and
      worklist_steps (scraped from the Stats printout like part_b), plus the
      winning abstraction's body/arity/utility for reference.

All stitch runs use an explicit subprocess timeout; a timeout is recorded as
{"timed_out": true} rather than crashing the sweep.
"""

import argparse
import json
import os
import re
import subprocess
import time

import part_a

HERE = os.path.dirname(os.path.abspath(__file__))
BINARY = "/home/user/mini-stitch/stitch/target/release/compress"
OUT = os.path.join(HERE, "results_large.jsonl")


def append(res):
    with open(OUT, "a") as f:
        f.write(json.dumps(res) + "\n")
    print(json.dumps(res, indent=2))


def cmd_au(args):
    res = part_a.run(args.corpus, args.name, args.prefix, args.budget)
    res["kind"] = "au"
    append(res)


def cmd_stitch(args):
    res = {"kind": "stitch", "corpus": args.name, "path": args.corpus,
           "fmt": args.fmt, "max_arity": args.arity}
    out = os.path.join(HERE, "tmp",
                       "stitch-out-%s-a%d.json" % (args.name, args.arity))
    cmd = [BINARY, args.corpus, "--max-arity=%d" % args.arity,
           "--iterations=1", "--out=%s" % out]
    if args.fmt != "programs-list":
        cmd.append("--fmt=%s" % args.fmt)
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              timeout=args.timeout)
    except subprocess.TimeoutExpired:
        res["timed_out"] = True
        res["wall_seconds"] = round(time.perf_counter() - t0, 3)
        append(res)
        return
    res["wall_seconds"] = round(time.perf_counter() - t0, 3)
    if proc.returncode != 0:
        res["error"] = proc.stderr[-500:]
        append(res)
        return
    m = re.search(r"worklist_steps: (\d+)", proc.stdout)
    res["worklist_steps"] = int(m.group(1)) if m else None
    with open(out) as f:
        result = json.load(f)
    abstractions = result.get("abstractions", [])
    if abstractions:
        w = abstractions[0]
        res["winner_body"] = w["body"]
        res["winner_arity"] = w["arity"]
        res["winner_utility"] = w["utility"]
    else:
        res["no_abstraction"] = True
    append(res)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)

    a = sub.add_parser("au")
    a.add_argument("corpus")
    a.add_argument("--name", required=True)
    a.add_argument("--prefix", type=int, default=None)
    a.add_argument("--budget", type=float, default=600.0)
    a.set_defaults(func=cmd_au)

    s = sub.add_parser("stitch")
    s.add_argument("corpus")
    s.add_argument("--name", required=True)
    s.add_argument("--arity", type=int, default=2)
    s.add_argument("--fmt", default="programs-list",
                   choices=["programs-list", "dreamcoder"])
    s.add_argument("--timeout", type=float, default=600.0)
    s.set_defaults(func=cmd_stitch)

    args = ap.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
