#!/usr/bin/env python3
"""Conjecture the inclusion/equivalence structure of the 120 cube logics.

The logics are `LogicE<base><suffix>` where `<base>` ranges over the eight classical
bases (subsets of {M, C, N}) and `<suffix>` over the fifteen axiom combinations of
{T, D, B, 4, 5} axiomatising the fifteen distinct normal modal logics over `K`.

Method
------
*Semantic separations.*  For a finite neighborhood frame `F` on `n` worlds the
validity of an axiom *scheme* is decided by instantiating its variables with all
truth sets (arbitrary subsets of the worlds), because valuations are arbitrary.
If `F` validates every axiom of `L2` but refutes some axiom scheme of `L1`, then
`L1 ⊄ L2` (the same argument as the `frame_*.not_valid_axiom*` proofs in the
repository).  We enumerate frames and record their validity *profiles*
(subsets of {M, C, N, T, D, B, 4, 5} valid on the frame); the pair matrix then
follows from the achieved profiles alone.

*Syntactic inclusions.*  If the axiom letters of `L1` are a subset of those of
`L2`, then `L1 ⊆ L2` is provable by `Hilbert.subset_of_subset_axioms`.

Pairs with no separating frame and no letter-subset inclusion are reported as
conjectures (requiring a Hilbert derivation, or a larger separating frame).

Output: human-readable summary on stdout, JSON dump in `zoo/conjecture_result.json`.
"""

import itertools
import json
import random
import sys
from collections import defaultdict

LETTERS = "MCNTDB45"  # canonical order

BASES = ["", "M", "C", "N", "MC", "MN", "CN", "MCN"]
SUFFIXES = ["", "T", "D", "B", "4", "5", "TB", "T4", "T5",
            "DB", "D4", "D5", "D45", "45", "B4"]

LOGICS = {}  # name -> frozenset of letters
for base in BASES:
    for suf in SUFFIXES:
        LOGICS["E" + base + suf] = frozenset(base + suf)


# ---------------------------------------------------------------------------
# Frame profiles
# ---------------------------------------------------------------------------

def profile(n, cols):
    """Validity profile of the frame with `n` worlds and neighborhoods `cols`.

    `cols[w]` is a bitmask over the 2^n subsets (subset X is a world-bitmask,
    used as bit index).  Returns a frozenset of valid axiom letters.
    """
    full = (1 << n) - 1
    nsub = 1 << n
    boxes = [0] * nsub
    for x in range(nsub):
        b = 0
        for w in range(n):
            if (cols[w] >> x) & 1:
                b |= 1 << w
        boxes[x] = b

    valid = set()
    # M: box(X∩Y) ⊆ box(X) ∩ box(Y)
    if all(boxes[x & y] & ~(boxes[x] & boxes[y]) == 0
           for x in range(nsub) for y in range(nsub)):
        valid.add("M")
    # C: box(X) ∩ box(Y) ⊆ box(X∩Y)
    if all((boxes[x] & boxes[y]) & ~boxes[x & y] == 0
           for x in range(nsub) for y in range(nsub)):
        valid.add("C")
    # N: box(W) = W
    if boxes[full] == full:
        valid.add("N")
    dia = [full & ~boxes[full & ~x] for x in range(nsub)]
    # T: box(X) ⊆ X
    if all(boxes[x] & ~x == 0 for x in range(nsub)):
        valid.add("T")
    # D: box(X) ⊆ dia(X)
    if all(boxes[x] & ~dia[x] == 0 for x in range(nsub)):
        valid.add("D")
    # B: X ⊆ box(dia(X))
    if all(x & ~boxes[dia[x]] == 0 for x in range(nsub)):
        valid.add("B")
    # 4: box(X) ⊆ box(box(X))
    if all(boxes[x] & ~boxes[boxes[x]] == 0 for x in range(nsub)):
        valid.add("4")
    # 5: dia(X) ⊆ box(dia(X))
    if all(dia[x] & ~boxes[dia[x]] == 0 for x in range(nsub)):
        valid.add("5")
    return frozenset(valid)


ACHIEVED = {}  # profile -> witness (n, cols)


def record(n, cols):
    cols = tuple(cols)
    p = profile(n, cols)
    old = ACHIEVED.get(p)
    if old is None or (n, cols) < old:
        ACHIEVED[p] = (n, tuple(cols))


# --- local (per-world) pools for |W| = 3 -----------------------------------

def pools_n3():
    n = 3
    nsub = 1 << n
    allc = range(1 << nsub)

    def upward(c):
        return all(not ((c >> s) & 1) or ((c >> t) & 1)
                   for s in range(nsub) for t in range(nsub) if s & t == s)

    def intclosed(c):
        mem = [s for s in range(nsub) if (c >> s) & 1]
        return all((c >> (s & t)) & 1 for s in mem for t in mem)

    def nocomp(c):
        full = nsub - 1
        return all(not ((c >> s) & 1) or not ((c >> (full ^ s)) & 1)
                   for s in range(nsub))

    up = [c for c in allc if upward(c)]
    ci = [c for c in allc if intclosed(c)]
    nc = [c for c in allc if nocomp(c)]
    hasfull = [c for c in allc if (c >> (nsub - 1)) & 1]
    tw = [[c for c in allc
           if all(not ((c >> s) & 1) or ((s >> w) & 1) for s in range(nsub))]
          for w in range(3)]
    return up, ci, nc, hasfull, tw


def enumerate_frames():
    # |W| = 1, 2: exhaustive
    for n in (1, 2):
        nsub = 1 << n
        for cols in itertools.product(range(1 << nsub), repeat=n):
            record(n, cols)

    up, ci, nc, hasfull, tw = pools_n3()
    print(f"n=3 pools: monotone {len(up)}, ∩-closed {len(ci)}, "
          f"no-complement {len(nc)}, contains-unit {len(hasfull)}", file=sys.stderr)

    # |W| = 3, exhaustive over frames whose worlds all satisfy one local property
    for pool, label, cap in [(up, "M", None), (nc, "D", None)]:
        for cols in itertools.product(pool, repeat=3):
            record(3, cols)
    for cols in itertools.product(tw[0], tw[1], tw[2]):  # T
        record(3, cols)

    rng = random.Random(0)
    # ∩-closed and contains-unit pools are large: sample within them
    for pool, k in [(ci, 400_000), (hasfull, 400_000)]:
        for _ in range(k):
            record(3, (rng.choice(pool), rng.choice(pool), rng.choice(pool)))
    # plain random |W| = 3 frames
    for _ in range(400_000):
        record(3, (rng.randrange(256), rng.randrange(256), rng.randrange(256)))

    # augmentations of Kripke frames, |W| ≤ 4: N(w) = { X ⊇ R[w] }
    for n in (1, 2, 3, 4):
        nsub = 1 << n
        for rel in itertools.product(range(nsub), repeat=n):  # rel[w] = R[w] mask
            cols = []
            for w in range(n):
                c = 0
                for x in range(nsub):
                    if x & rel[w] == rel[w]:
                        c |= 1 << x
                cols.append(c)
            record(n, cols)


# ---------------------------------------------------------------------------
# Pair matrix and report
# ---------------------------------------------------------------------------

def main():
    enumerate_frames()
    profiles = list(ACHIEVED.keys())
    print(f"achieved profiles: {len(profiles)}", file=sys.stderr)

    names = sorted(LOGICS, key=lambda s: (len(s), [LETTERS.index(c) for c in s[1:]]))

    # separated[(a, b)] = witness profile refuting a ⊆ b, if any
    def separation(a, b):
        ax_a, ax_b = LOGICS[a], LOGICS[b]
        for p in profiles:
            if ax_b <= p and not ax_a <= p:
                return p
        return None

    sep = {}
    for a in names:
        for b in names:
            if a == b:
                continue
            w = separation(a, b)
            if w is not None:
                sep[(a, b)] = w

    def included(a, b):  # conjectured a ⊆ b
        return a == b or (a, b) not in sep

    # equivalence classes under mutual conjectured inclusion
    classes = []
    assigned = {}
    for a in names:
        for cl in classes:
            r = cl[0]
            if included(a, r) and included(r, a):
                cl.append(a)
                assigned[a] = cl
                break
        else:
            classes.append([a])
            assigned[a] = classes[-1]

    # order classes; transitive reduction for the Hasse diagram
    reps = [cl[0] for cl in classes]
    below = {r: {s for s in reps if s != r and included(s, r)} for r in reps}
    hasse = []
    for r in reps:
        for s in below[r]:
            if not any(s in below[t] and t in below[r] for t in reps
                       if t != r and t != s):
                hasse.append((s, r))

    # report ---------------------------------------------------------------
    multi = [cl for cl in classes if len(cl) > 1]
    print(f"logics: {len(names)}")
    print(f"conjectured equivalence classes: {len(classes)}")
    print(f"nontrivial classes ({len(multi)}):")
    for cl in sorted(multi, key=lambda c: (len(c[0]), c[0])):
        # which equalities are letter-trivial vs need derivations
        print("  " + " = ".join(cl))
    print(f"\nHasse edges (conjectured strict inclusions): {len(hasse)}")

    # inclusion obligations: conjectured a ⊆ b that are NOT letter-subset
    obligations = []
    for a in names:
        for b in names:
            if a != b and included(a, b) and not LOGICS[a] <= LOGICS[b]:
                obligations.append((a, b, sorted(LOGICS[a] - LOGICS[b])))
    print(f"\nconjectured inclusions needing a Hilbert derivation: {len(obligations)}")

    def fr(w):
        n, cols = w
        return {"worlds": n,
                "neighborhoods": [[x for x in range(1 << n) if (c >> x) & 1]
                                  for c in cols]}

    result = {
        "logics": {a: sorted(LOGICS[a]) for a in names},
        "classes": [sorted(cl) for cl in classes],
        "hasse": [{"from": s, "to": r} for (s, r) in hasse],
        "separations": [
            {"notincluded": a, "in": b, "profile": "".join(sorted(p)),
             "witness": fr(ACHIEVED[p])}
            for (a, b), p in sorted(sep.items())
        ],
        "derivation_obligations": [
            {"sub": a, "sup": b, "derive": d} for (a, b, d) in obligations
        ],
        "profiles": {"".join(sorted(p)): fr(w) for p, w in ACHIEVED.items()},
    }
    with open("zoo/conjecture_result.json", "w") as f:
        json.dump(result, f, indent=1, ensure_ascii=False)
    print("\nwrote zoo/conjecture_result.json")


if __name__ == "__main__":
    main()
