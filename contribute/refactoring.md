# ModalLogic Writing & Refactoring Guide

Guidelines for writing and refactoring Lean code in this repository. The goal is to simplify the essential structure of the code while preserving the mathematical content and making proofs easier for humans to maintain.

As in [style.md](./style.md), these are house-style conventions rather than mathematical requirements. AI coding agents should follow them closely.

## Reporting

After a refactor, report the size change: how many lines the relevant code went from and to, and the percentage reduction.

## Priorities

1. Keep the essential structure of the code as simple as possible.
2. Prioritize readability of code and tactics next.
3. Treat shorter code as valuable, but only after structural simplicity and readability.

## Rules

### Lemmas and definitions

- Extract and collect lemmas that are reused multiple times, or that can reasonably be packaged for reuse.

- Avoid redundant definitions and proofs: do not introduce definitions or proofs obtainable from existing ones by at most about two layers of nesting, unless they are used repeatedly or occur frequently.

- Do not split out one-off working lemmas that are not expected to be reused. Keep them inside the proof where they are used.

- Merge `private` helper lemmas of the same shape that have been copied from section to section into one general version parameterized by what differs. If a specialization follows from the general version by a one-line term, derive it; otherwise drop the specialization and rewrite its call sites to use the general version with explicit arguments.

- Merge short API files — a single definition plus its basic lemmas — into the corresponding namespace of the file that defines the underlying notion, delete the file, and redirect the downstream imports.

- Delete a compatibility shim once the definition it stands in for can be used directly, replacing the calls that went through it.

### Tactics

- Avoid tactics that harm readability as much as possible, such as `rw`, non-terminal `simp`, `simp only ...`, and `simp at ...`. They may be used when avoiding them would make the proof significantly more complicated or artificial. Consider using `have ...`, `suffices`, and similar structure instead.

- Use terminal tactics such as `grind`, `simp_all`, `tauto`, and `ring` actively at the end of proofs. If a proof follows from elementary logic about simple types, consider trying `grind`.

- If a flexible tactic warning appears, such as for `simp ...`, explicitly state the simplified target using `suffices` or `change`.

### Notation

- Use field notation whenever possible. For a term `t : TypeName` and a function `f : TypeName → Range`, prefer `t.f` to `f t`.

- Use symbolic shorthand actively. For example, `Quotient.mk s x` is long, so use `⟦x⟧` whenever possible.

- Drop explicit universe annotations, inferable casts and redundant parentheses where elaboration can recover them.

### Constructivity

- Prefer constructive proofs that do not depend on `classical` whenever possible.

## Redundant terms

The following proofs and definitions are bad examples. Rewrite them into the better forms shown below. Similar syntax should be treated in the same way.

- ```lean
  by exact t
  ```

  Prefer:

  ```lean
  t
  ```

- ```lean
  by
    intro x y
    exact t
  ```

  Prefer:

  ```lean
  fun x y ↦ t
  ```

- ```lean
  refine ⟨x, y, ?_, z, ?_⟩
  · tactic1
  · tactic2
  ```

  Prefer:

  ```lean
  refine ⟨x, y, by tactic1, z, by tactic2⟩
  ```

- ```lean
  apply f
  exact g (h k)
  ```

  Prefer:

  ```lean
  exact f (g (h k))
  ```
