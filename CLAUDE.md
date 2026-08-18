This repository is an in-progress replication of a miniature version of the stitch library learning system. The system is implemented with AI assistance.

The goal of the miniature version is to exhibit the core algorithm and essential optimizations while stripping away unnecessary complexities.

We can leave out of consideration:
 - Parallelism
 - Constant-factor improvements (e.g. using Rust vs a higher-level language)

notes/ contains notes and reflections written by Claude or Codex, named with a <YYYY>-<MM>-<DD>-<TTTT>-<slug>.md format.
The stitch paper is "Top-Down Synthesis for Library Learning" (POPL 2023),
https://arxiv.org/abs/2211.16605 (not checked in; keep a local copy as stitch.pdf,
which is gitignored)
stitch/ is a git submodule with the real stitch implementation
todo.md contains the current plan

Claude or Codex should dispatch detailed implementation, debugging, and testing work to subagents (opus or sonnet as appropriate) to avoid exhausting the main conversation context over long-running work. The main session should however take responsiblity for high-level direction, design, and review.

