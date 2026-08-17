This repository is an in-progress replication of a miniature version of the stitch library learning system. The system is implemented with AI assistance.

The goal of the miniature version is to exhibit the core algorithm and essential optimizations while stripping away unnecessary complexities.

We can leave out of consideration:
 - Parallelism
 - Constant-factor improvements (e.g. using Rust vs a higher-level language)

notes/ contains notes and reflections written by Claude or Codex, named with a <YYYY>-<MM>-<DD>-<TTTT>-<slug>.md format.
stitch.pdf is the original stitch paper
stitch/ is a git submodule with the real stitch implementation
todo.md contains the current plan