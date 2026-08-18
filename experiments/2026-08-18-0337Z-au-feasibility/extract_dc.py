"""extract_dc.py --- extract a flat programs-list from a DreamCoder-format file.

Replicates EXACTLY what stitch's own loader does for --fmt=dreamcoder
(stitch/src/formats.rs, InputFormat::Dreamcoder):

  1. collect every DSL production whose expression starts with '#'
     (these are DreamCoder inventions, written inline as `#(lambda ...)`);
  2. sort them by increasing string length and name them
     dreamcoder_abstraction_0, dreamcoder_abstraction_1, ...;
  3. in every frontier program, textually replace each invention string by
     its name, LONGEST FIRST (so inventions that contain earlier inventions
     as substrings are replaced before their sub-inventions can mangle them);
  4. assert no '#' remains in any program.

The result is the same token stream stitch itself compresses, so AU numbers
computed on the extracted list are comparable with stitch runs on the
original file. Task grouping is NOT preserved (programs-list format has no
tasks; stitch then treats each program as its own task).

Usage:
    python3 extract_dc.py IN.json OUT.json
Prints a one-line summary (n tasks, n programs, n inventions replaced).
"""

import json
import sys


def extract(in_path):
    with open(in_path) as f:
        d = json.load(f)
    frontiers = d["frontiers"]
    dsl = d.get("DSL", {})
    invs = [p["expression"] for p in dsl.get("productions", [])
            if p["expression"].startswith("#")]
    invs.sort(key=len)  # increasing length, same as stitch
    named = [("dreamcoder_abstraction_%d" % i, s) for i, s in enumerate(invs)]
    programs = []
    ntasks = 0
    for fr in frontiers:
        ntasks += 1
        for pr in fr["programs"]:
            p = pr["program"]
            for name, s in reversed(named):  # longest first, same as stitch
                p = p.replace(s, name)
            assert "#" not in p, "unreplaced invention in %s" % p
            programs.append(p)
    return programs, ntasks, len(named)


def main():
    in_path, out_path = sys.argv[1], sys.argv[2]
    programs, ntasks, ninvs = extract(in_path)
    with open(out_path, "w") as f:
        json.dump(programs, f)
    print(json.dumps({"in": in_path, "out": out_path, "tasks": ntasks,
                      "programs": len(programs), "inventions_replaced": ninvs}))


if __name__ == "__main__":
    main()
