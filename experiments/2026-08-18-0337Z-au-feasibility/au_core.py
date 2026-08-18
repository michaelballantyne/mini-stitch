"""au_core.py --- hash-consed arena, stitch-syntax parser, de Bruijn-aware
shifting, anti-unification (Plotkin lgg), and pattern matching.

Mirrors the semantics of /home/user/mini-stitch/src/expr.rkt:

  * (a b c) is curried left-associated application; `app` is NOT a keyword.
  * (lam e) / (lambda e): lambda with exactly one body; $i de Bruijn var;
    #i abstraction variable (ivar); other atoms are primitives.
  * Fused-lambda tags (lam_1, $0_1) raise FusedTagError -> corpus is skipped.

Node encodings (interned tuples in one shared arena):
    ('prim', name)   ('var', i)   ('ivar', i)
    ('app', f, x)    ('lam', b)
    ('kvar', key)    # anti-unification variable, keyed by a hashable key
                     # (patterns only; never parsed from input)

Shifting (the load-bearing de Bruijn subtlety): shift(t, m) is the subtree t
as seen from a match root with m lambdas between the root and t. Free var $d
of t (d relative to t's own root, i.e. after subtracting binders internal to
t) becomes sentinel ivar #d if d < m, else var $(d-m). Bound vars untouched.
Two hole positions see "the same argument" iff their shifted ids are equal.
"""

import sys

sys.setrecursionlimit(1_000_000)


class FusedTagError(ValueError):
    pass


class Arena:
    def __init__(self):
        self.nodes = []          # idx -> node tuple
        self.intern = {}         # node tuple -> idx
        self._max_free = {}      # idx -> max free de Bruijn index, -1 if none
        self._has_ivar = {}      # idx -> bool (contains ivar / sentinel)
        self._shift_memo = {}    # (idx, m) -> idx
        self._au_memo = {}       # (a, b, depth) -> pattern idx (non-root calls)
        self._canon_memo = {}    # pattern idx -> canonical pattern idx
        self.au_root_calls = 0   # top-level au invocations (one per pair)

    def add(self, node):
        idx = self.intern.get(node)
        if idx is None:
            idx = len(self.nodes)
            self.nodes.append(node)
            self.intern[node] = idx
        return idx

    # ------------------------------------------------------------------
    # Parsing (tokenizer + group parser, mirroring expr.rkt)
    # ------------------------------------------------------------------

    def parse(self, s):
        """Parse one program string, interning every subtree. Returns root idx."""
        toks = []
        i, n = 0, len(s)
        while i < n:
            ch = s[i]
            if ch.isspace():
                i += 1
            elif ch == '(':
                toks.append('(')
                i += 1
            elif ch == ')':
                toks.append(')')
                i += 1
            else:
                j = i
                while j < n and not s[j].isspace() and s[j] not in '()':
                    j += 1
                toks.append(s[i:j])
                i = j
        if not toks:
            raise ValueError("empty program text")
        idx, rest = self._parse_group(toks, 0, in_parens=False)
        if rest != len(toks):
            raise ValueError("mismatched parentheses in: %s" % s)
        return idx

    def _atom(self, a):
        if a in ('lam', 'lambda'):
            return 'lam-keyword'
        if a.startswith('lam_') or a.startswith('lambda_'):
            raise FusedTagError("fused-lambda tags are not supported: %s" % a)
        if a.startswith('$'):
            rest = a[1:]
            if rest.isdigit():
                return self.add(('var', int(rest)))
            if '_' in rest:
                parts = rest.split('_')
                if len(parts) == 2 and parts[0].isdigit() and parts[1].isdigit():
                    raise FusedTagError("variable tags are not supported: %s" % a)
            raise ValueError("malformed de Bruijn variable: %s" % a)
        if a.startswith('#'):
            rest = a[1:]
            if not rest.isdigit():
                raise ValueError("malformed abstraction variable: %s" % a)
            return self.add(('ivar', int(rest)))
        return self.add(('prim', a))

    def _parse_group(self, toks, pos, in_parens):
        items = []
        while True:
            if pos == len(toks):
                if in_parens:
                    raise ValueError("mismatched parentheses")
                return self._combine(items), pos
            t = toks[pos]
            if t == ')':
                if not in_parens:
                    raise ValueError("unexpected `)`")
                return self._combine(items), pos + 1
            if t == '(':
                idx, pos = self._parse_group(toks, pos + 1, True)
                items.append(idx)
            else:
                items.append(self._atom(t))
                pos += 1

    def _combine(self, items):
        if not items:
            raise ValueError("empty group ()")
        if items[0] == 'lam-keyword':
            if len(items) != 2:
                raise ValueError("`lam` must be applied to exactly one argument")
            return self.add(('lam', items[1]))
        if 'lam-keyword' in items:
            raise ValueError("`lam` must be the head of its group")
        f = items[0]
        for x in items[1:]:
            f = self.add(('app', f, x))
        return f

    # ------------------------------------------------------------------
    # Printing (mirrors expr->string: application spines flattened)
    # ------------------------------------------------------------------

    def to_string(self, idx):
        out = []

        def emit(idx, left_of_app):
            n = self.nodes[idx]
            k = n[0]
            if k == 'var':
                out.append('$%d' % n[1])
            elif k == 'ivar':
                out.append('#%d' % n[1])
            elif k == 'prim':
                out.append(n[1])
            elif k == 'kvar':
                out.append('?%r' % (n[1],))
            elif k == 'app':
                if not left_of_app:
                    out.append('(')
                emit(n[1], True)
                out.append(' ')
                emit(n[2], False)
                if not left_of_app:
                    out.append(')')
            else:  # lam
                out.append('(lam ')
                emit(n[1], False)
                out.append(')')

        emit(idx, False)
        return ''.join(out)

    # ------------------------------------------------------------------
    # Analyses
    # ------------------------------------------------------------------

    def max_free(self, idx):
        """Largest free de Bruijn index of the subtree, -1 if closed.
        (kvars and ivars contribute nothing.)"""
        r = self._max_free.get(idx)
        if r is not None:
            return r
        n = self.nodes[idx]
        k = n[0]
        if k == 'var':
            r = n[1]
        elif k == 'app':
            r = max(self.max_free(n[1]), self.max_free(n[2]))
        elif k == 'lam':
            b = self.max_free(n[1])
            r = b - 1 if b >= 1 else -1
        else:
            r = -1
        self._max_free[idx] = r
        return r

    def has_ivar(self, idx):
        """Does any ivar #i occur in the subtree? For a shifted argument this
        is exactly 'contains a sentinel', i.e. the argument captures."""
        r = self._has_ivar.get(idx)
        if r is not None:
            return r
        n = self.nodes[idx]
        k = n[0]
        if k == 'ivar':
            r = True
        elif k == 'app':
            r = self.has_ivar(n[1]) or self.has_ivar(n[2])
        elif k == 'lam':
            r = self.has_ivar(n[1])
        else:
            r = False
        self._has_ivar[idx] = r
        return r

    def tree_size(self, idx):
        """Number of tree nodes of the subtree viewed as a tree (per
        occurrence, ignoring sharing)."""
        n = self.nodes[idx]
        k = n[0]
        if k == 'app':
            return 1 + self.tree_size(n[1]) + self.tree_size(n[2])
        if k == 'lam':
            return 1 + self.tree_size(n[1])
        return 1

    # ------------------------------------------------------------------
    # Shifting
    # ------------------------------------------------------------------

    def shift(self, idx, m):
        """The subtree at idx as seen from a match root m lambdas above it:
        free $d (relative to idx's root) -> sentinel #d if d < m, else $(d-m).
        Mirrors shift-arg in expr.rkt."""
        if m == 0:
            return idx
        key = (idx, m)
        r = self._shift_memo.get(key)
        if r is not None:
            return r

        def walk(idx, depth):
            # nothing in this subtree escapes past its own binders -> unchanged
            if self.max_free(idx) < depth:
                return idx
            n = self.nodes[idx]
            k = n[0]
            if k == 'var':
                i = n[1]
                d = i - depth  # index relative to the argument's root
                if i < depth:
                    return idx            # bound inside the argument
                if d < m:
                    return self.add(('ivar', d))   # points at a crossed lam
                return self.add(('var', i - m))    # points above the root
            if k == 'app':
                return self.add(('app', walk(n[1], depth), walk(n[2], depth)))
            if k == 'lam':
                return self.add(('lam', walk(n[1], depth + 1)))
            return idx  # prim / ivar / kvar

        r = walk(idx, 0)
        self._shift_memo[key] = r
        return r

    # ------------------------------------------------------------------
    # Anti-unification (Plotkin lgg), de Bruijn-aware
    # ------------------------------------------------------------------
    #
    # au(a, b, depth) produces a pattern whose variables are kvar nodes KEYED
    # by the pair (shift(a, depth), shift(b, depth)) of the mismatching
    # subtrees. Keying by the shifted pair is what makes (1) repeated keys
    # share a variable (multiuse bodies like (#0 #0 #0)) and (2) the memo
    # sound across top-level pairs: the key is context-independent, so an
    # au(a,b,depth) result means the same thing wherever it is reused.
    # Canonical variable naming (by first occurrence) is applied afterwards,
    # per top-level result, by canonicalize().
    #
    # kvar-vs-anything (used when folding the lgg of a whole SET of trees:
    # the accumulator is a pattern containing kvars) pairs the old key with
    # the newly seen shifted subtree, so a variable stays merged iff every
    # tree in the set agreed at that position.

    def au(self, a, b, depth=0, _root=True):
        if a == b:
            return a  # identical interned subtrees stay fully concrete
        if _root:
            self.au_root_calls += 1
            key = None
        else:
            key = (a, b, depth)
            r = self._au_memo.get(key)
            if r is not None:
                return r
        na = self.nodes[a]
        nb = self.nodes[b]
        ka, kb = na[0], nb[0]
        if ka == 'kvar':
            # folding case: accumulator variable meets a new subtree
            r = self.add(('kvar', ('F', a, self.shift(b, depth))))
        elif ka == 'app' and kb == 'app':
            r = self.add(('app',
                          self.au(na[1], nb[1], depth, _root=False),
                          self.au(na[2], nb[2], depth, _root=False)))
        elif ka == 'lam' and kb == 'lam':
            r = self.add(('lam', self.au(na[1], nb[1], depth + 1, _root=False)))
        else:
            r = self.add(('kvar', ('P', self.shift(a, depth), self.shift(b, depth))))
        if key is not None:
            self._au_memo[key] = r
        return r

    def au_memo_size(self):
        return len(self._au_memo)

    def canonicalize(self, p):
        """Rename kvars to ivars #0,#1,... by first occurrence in a leftmost
        (fun-before-arg) traversal. Memoized on the interned pattern id, which
        is sound because the canonical form depends only on the pattern."""
        r = self._canon_memo.get(p)
        if r is not None:
            return r
        mapping = {}

        def walk(idx):
            n = self.nodes[idx]
            k = n[0]
            if k == 'kvar':
                key = n[1]
                if key not in mapping:
                    mapping[key] = len(mapping)
                return self.add(('ivar', mapping[key]))
            if k == 'app':
                f = walk(n[1])
                x = walk(n[2])
                return self.add(('app', f, x))
            if k == 'lam':
                return self.add(('lam', walk(n[1])))
            return idx

        r = walk(p)
        self._canon_memo[p] = r
        return r

    def canonicalize_ivars(self, p):
        """Same renaming for a pattern already written with ivars (e.g. a
        stitch abstraction body), so both sides compare modulo renaming."""
        mapping = {}

        def walk(idx):
            n = self.nodes[idx]
            k = n[0]
            if k == 'ivar':
                i = n[1]
                if i not in mapping:
                    mapping[i] = len(mapping)
                return self.add(('ivar', mapping[i]))
            if k == 'app':
                f = walk(n[1])
                x = walk(n[2])
                return self.add(('app', f, x))
            if k == 'lam':
                return self.add(('lam', walk(n[1])))
            return idx

        return walk(p)

    def regeneralize_free_vars(self, p):
        """Replace every de Bruijn var leaf that is free relative to the
        pattern root (i.e. $i at pattern depth d with i >= d) by a variable
        keyed by its root-relative index, merging occurrences with the same
        index. This mimics stitch's ban on free de Bruijn vars in abstraction
        bodies: where the true lgg keeps a shared free var concrete, stitch is
        forced to introduce an abstraction variable for it instead."""

        def walk(idx, depth):
            n = self.nodes[idx]
            k = n[0]
            if k == 'var' and n[1] >= depth:
                return self.add(('kvar', ('V', n[1] - depth)))
            if k == 'app':
                f = walk(n[1], depth)
                x = walk(n[2], depth)
                return self.add(('app', f, x))
            if k == 'lam':
                return self.add(('lam', walk(n[1], depth + 1)))
            return idx

        return walk(p, 0)

    def pattern_stats(self, p):
        """(#distinct variables, #variable occurrences) of a canonical (ivar)
        or kvar pattern."""
        seen = set()
        occ = 0

        def walk(idx):
            nonlocal occ
            n = self.nodes[idx]
            k = n[0]
            if k in ('ivar', 'kvar'):
                seen.add(n[1])
                occ += 1
            elif k == 'app':
                walk(n[1])
                walk(n[2])
            elif k == 'lam':
                walk(n[1])

        walk(p)
        return len(seen), occ

    # ------------------------------------------------------------------
    # Matching: is corpus subtree t an instance of pattern (with ivars)?
    # ------------------------------------------------------------------

    def match(self, pat, t):
        """Return (bindings, captures) if t matches pat, else None.
        bindings maps ivar index -> shifted argument id; consistency is
        de Bruijn-aware: the argument seen at a hole under `depth` crossed
        pattern-lambdas is shift(subtree, depth). captures = some bound
        argument contains a sentinel (cannot be passed at a call site)."""
        bindings = {}

        def walk(p, s, depth):
            np_ = self.nodes[p]
            k = np_[0]
            if k == 'ivar':
                v = self.shift(s, depth)
                i = np_[1]
                prev = bindings.get(i)
                if prev is None:
                    bindings[i] = v
                    return True
                return prev == v
            ns = self.nodes[s]
            if k == 'app':
                return (ns[0] == 'app'
                        and walk(np_[1], ns[1], depth)
                        and walk(np_[2], ns[2], depth))
            if k == 'lam':
                return ns[0] == 'lam' and walk(np_[1], ns[1], depth + 1)
            return p == s  # prim / var leaf: interned equality

        if not walk(pat, t, 0):
            return None
        captures = any(self.has_ivar(v) for v in bindings.values())
        return bindings, captures


def load_corpus(path, prefix=None):
    import json
    with open(path) as f:
        programs = json.load(f)
    if prefix is not None:
        programs = programs[:prefix]
    return programs


def build_arena(programs):
    """Parse programs into a fresh arena. Returns (arena, roots, span)."""
    a = Arena()
    roots = [a.parse(p) for p in programs]
    span = len(a.nodes)
    return a, roots, span
