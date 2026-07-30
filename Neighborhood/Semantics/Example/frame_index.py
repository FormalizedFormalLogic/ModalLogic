#!/usr/bin/env python3
"""Canonical indices for neighborhood frames on a finite carrier.

A frame on `Fin n` is a function `𝒩 : Fin n → Set (Set (Fin n))`, so on a finite
carrier it is determined by finitely many bits and can be encoded as a number:

* a subset `S ⊆ Fin n` is the bitmask `m(S) = Σ_{i ∈ S} 2^i` (so `m(S) < 2^n`);
* a neighborhood family `𝒩 w ⊆ P(Fin n)` is the bitmask
  `f(w) = Σ_{S ∈ 𝒩 w} 2^(m(S))` (so `f(w) < B` with `B = 2^(2^n)`);
* the frame is the number `Σ_w f(w) · B^w` (world `0` in the least significant
  digit, base `B`).

Relabeling the worlds by a permutation `σ` of `Fin n` acts on a frame by
`𝒩' w = { σ[S] | S ∈ 𝒩 (σ⁻¹ w) }`, and two frames are isomorphic exactly when
some relabeling maps one to the other. The **canonical index** of a frame is
the minimum of the encodings over all `n!` relabelings; it is a complete
isomorphism invariant, so frames are named `frame_<n>_<canonical index>`.
The Lean definition carries whichever representative of the class is most
convenient — the index names the isomorphism class, not the labeling.

Usage:

    # canonical index (and a canonical representative) of a frame,
    # families given as a Python literal, one collection of subsets per world:
    ./frame_index.py canon '[[{0}], [{0},{1},{0,1}]]'

    # decode an index back to a frame and print it as a Lean definition:
    ./frame_index.py lean 2 78
"""

import itertools
import sys
from ast import literal_eval


def subset_mask(s: frozenset, n: int) -> int:
    return sum(1 << i for i in s)


def family_mask(fam, n: int) -> int:
    return sum(1 << subset_mask(s, n) for s in fam)


def encode(families, n: int) -> int:
    B = 1 << (1 << n)
    return sum(family_mask(fam, n) * B**w for w, fam in enumerate(families))


def relabel(families, sigma, n: int):
    """The frame with every world and every subset pushed through `sigma`."""
    inv = {sigma[i]: i for i in range(n)}
    return [
        [frozenset(sigma[i] for i in s) for s in families[inv[w]]]
        for w in range(n)
    ]


def canonical(families, n: int):
    """Minimum encoding over all relabelings, with a minimizing representative."""
    best = None
    for perm in itertools.permutations(range(n)):
        cand = relabel(families, perm, n)
        code = encode(cand, n)
        if best is None or code < best[0]:
            best = (code, cand)
    return best


def decode(n: int, code: int):
    B = 1 << (1 << n)
    families = []
    for _ in range(n):
        fmask, code = code % B, code // B
        fam = [
            frozenset(i for i in range(n) if smask >> i & 1)
            for smask in range(1 << n)
            if fmask >> smask & 1
        ]
        families.append(fam)
    return families


def lean_subset(s: frozenset, n: int) -> str:
    if not s:
        return "∅"
    if len(s) == n:
        return "Set.univ"
    return "{" + ", ".join(str(i) for i in sorted(s)) + "}"


def lean_def(families, n: int, code: int) -> str:
    fams = [
        "{" + ", ".join(lean_subset(s, n) for s in sorted(fam, key=lambda s: subset_mask(s, n))) + "}"
        if fam else "∅"
        for fam in families
    ]
    if all(f == fams[0] for f in fams):
        body = f"⟨fun _ => {fams[0]}⟩"
        return f"abbrev frame_{n}_{code} : Frame (Fin {n}) := {body}"
    arms = "\n".join(f"    | {w} => {f}" for w, f in enumerate(fams))
    return (
        f"abbrev frame_{n}_{code} : Frame (Fin {n}) :=\n"
        f"  ⟨fun w => match w with\n{arms}⟩"
    )


def parse_families(text: str):
    raw = literal_eval(text.replace("{}", "set()"))
    return [[frozenset(s) for s in fam] for fam in raw]


def main() -> None:
    match sys.argv[1:]:
        case ["canon", text]:
            families = parse_families(text)
            n = len(families)
            code, rep = canonical(families, n)
            print(f"canonical index: {code}")
            print(f"name           : frame_{n}_{code}")
            print(lean_def(rep, n, code))
        case ["lean", n, code]:
            n, code = int(n), int(code)
            print(lean_def(decode(n, code), n, code))
        case _:
            print(__doc__)
            sys.exit(1)


if __name__ == "__main__":
    main()
