# ModalLogic Coding Style

Coding conventions for the formal proofs in this repository. The guiding principle: proofs are read and maintained by humans, so write them the way the human maintainers read them.

As a baseline, follow the [Mathlib style guide](https://leanprover-community.github.io/contribute/style.html) (line length, indentation, spacing, naming, calc/tactic formatting, etc.). This document only records what is specific to this repository; where it differs from the Mathlib guide, this document takes precedence. For writing and refactoring conventions see [refactoring.md](./refactoring.md).

Human contributors need not follow this document to the letter — treat it as a description of the house style. 🤖 AI coding agents should follow it as closely as possible, especially the items marked 🤖: machine-generated proofs tend to drift toward a verbose, defensive style, and those items exist to counteract that drift.

## General conventions

- End each line of a proof with a semicolon (`;`) where it reads naturally.
- Omit type annotations that are trivially inferred. Leave an implicit whose type the later hypotheses pin down to autobound implicits instead of writing an explicit binder, and drop redundant type ascriptions and parentheses.
- Do not introduce implicit variables ad hoc in lemma statements. Declare them with `variable` in a `section`, and cut a new `section` when the context changes, rather than keeping one giant file-wide block. Keep only the implicits whose types genuinely diverge local to a lemma.
- `universe` declarations that are not needed can be omitted.

## Statements

**Write hypotheses as binders, not as a chain of `∀`/`→` discharged by `intro`.**

```lean
-- Avoid:
lemma foo : ∀ {Δ} (d : Derivation Δ), H → C := by intro Δ d h; …

-- Prefer:
lemma foo (d : Derivation Γ) (h : H) : C := by …
```

This includes hypotheses that the induction target depends on: `induction` generalizes those automatically, so there is no need to keep them behind `∀` or to open every case with an `intro` line. Where the original induction structure must be preserved, use `induction … generalizing …`, without listing the automatically generalized hypotheses.

**Write operations on a type `T` with dot notation, `T.f x`, not `f x` or `Namespace.f x`** — in the right-hand sides of recursive definitions and in applications to hypotheses as well. Put new lemmas in the namespace of the type they are about, and make the receiver the last explicit argument.

**Give a name to the specializations you keep repeating.** If a multi-argument monotonicity/transport lemma `mono (h₁ : α ≤ β) (h₂ : c ≤ c')` is called with `le_rfl` in one slot at several places, extract that specialization as a named wrapper (`mono_foo h := mono h le_rfl`) whose name says which parameter moves, and route every call site through it.

**Prefer stating a lemma about `f x` directly over parameterizing it by `(h : f x = c)`.** The abstract `c` forces `subst`/`omega` boilerplate at every use, whereas the direct form lets `simp`/`grind` compute `f x`. Where a call site really needs the equation, absorb it there with `suffices f x = c by subst this; …`.

## Proof style

Overall: construct terms directly when the type determines them, and hand the residue to automation — rather than opening holes in the goal and filling them one by one.

🤖 **Prefer direct term construction over `refine … ?_`.** Avoid `?_` where a term will do.

```lean
-- Avoid:
refine ⟨n, ?_, ?_⟩
· exact hn
· exact hn.le

-- Prefer:
exact ⟨n, hn, hn.le⟩
```

Reserve `refine` for components that genuinely need tactic work — and never write bound variables inside it:

```lean
-- Avoid:
refine ⟨hd, fun x hx => ?_⟩

-- Prefer:
refine ⟨hd, ?_⟩
intro x hx
```

**Use `use` to prove existentials** (`use n`) rather than `refine ⟨n, ?_⟩`, and **`obtain` to consume them** (`obtain ⟨n, hn⟩ := exists_bound f`) rather than `rcases`/`rintro`.

**Split a nested conjunction with `and_intros`**, not with `refine ⟨?_, ⟨?_, ?_⟩, ?_⟩` or repeated `constructor`.

**Share the proof of a symmetric pair** — where the two components of `⟨X, X⟩` are the same term — with `constructor <;> · …`.

🤖 **Use `show` only when the goal unfolds non-trivially.** Restating a goal that is already displayed in the needed form is noise.

🤖 **Do not open an induction case with a mechanical `simp only [<definition>]`.** Applications of a matching definition to a constructor reduce definitionally; try deleting the unfolding line first and keep it only if the case genuinely cannot proceed.

🤖 **Lean on automation for the final assembly.** State the few needed facts as `have`s and pass them to a tactic (`grind`, `simp`) instead of hand-chaining compositions. In an induction, try `grind` or `simp_all` on the base cases and the plain recursive cases before writing anything by hand.

🤖 **Inline small combinatorial side conditions as `(by grind)` at the point of use** — constructor distinctness, membership across `insert`/`erase` — instead of building them up with a chain of `have`s. Make that possible by keeping the recurring trivial facts as one-line lemmas tagged `@[simp, grind .]` (`@[grind =]` for equations) in a dedicated section; where an existing lemma only needs the attribute, `attribute [grind =] …` suffices. Prove `Finset` inclusions with the standard template

```lean
intro x; simp only [Finset.mem_insert, Finset.mem_erase]; grind
```

rather than case-splitting by hand with `rcases`.

**Reuse the name of an induction hypothesis you consume immediately**: `replace ih := ih h` rather than a fresh `have`.

🤖 **Keep proofs short; extract lemmas.** A tactic block beyond roughly thirty lines should be split: promote intermediate `have`s to stand-alone (possibly `private`) lemmas.

**Prove a `List.TFAE` bundle only where it reads well**, and cut the individual implications you actually reuse out as named lemmas: referring to `foo_TFAE.out 1 0` elsewhere breaks as soon as the order of the list changes.

**Shorten a long expression that recurs with `local notation`**, e.g. `local notation "ω₀" => Ordinal.omega0`. Conversely, do not introduce an `abbrev` whose right-hand side is already short and readable.

## Naming

- Lemma and theorem names are `snake_case`. For connectives, name them after the constructors of the implementation (`and`/`or`/`all`/`exs`), not after the notation of the paper (`Conj`/`Disj`). Left/right variants take `_left`/`_right`.
- A lemma that exists only as the inductive core of a main lemma is named `<main>Aux`.
- Notation from the source paper is renamed to the implementation's names in comments and docstrings. The one exception is the docstring of the definition itself, where the origin of the alternative name may be explained. Idiomatic abbreviations need no renaming.

🤖 Name intermediate `have`s with short positional names (`h₁`, `h₂`, …) or conventional ones (`hp`, `ih`), and let the type annotation carry the meaning. Do not give every step a one-shot descriptive compound name — it duplicates the type and goes stale under refactoring. A descriptive name is warranted only when the fact is referred to several times.

## File and module organization

**Do not create aggregator files.** When splitting a module `Foo.lean` into submodules under `Foo/`, delete `Foo.lean` rather than leaving it as a list of `public import Foo.A`, `public import Foo.B`; downstream files import the submodules they need. The all-import root file generated by `mk_all` already guarantees that every module is built.

**Every fact about a concrete example frame lives in that frame's own module** under
`Semantics/Example/` — its definition, its frame-condition instances, and the axioms it refutes.
The per-logic modules import the example frames they use instead of declaring ad hoc instances
about them.

**Example frames are named systematically as `frame_<n>_<index>`** (a root-level name, e.g.
`frame_2_78 : Frame (Fin 2)`), where the index is the canonical encoding of the frame's
isomorphism class: encode each world's neighborhood family as a bitmask over subset bitmasks,
read the worlds as digits in base `2^(2^n)`, and take the minimum over all relabelings of the
carrier. The module is named after the frame (`Semantics/Example/Frame2_78.lean`). Compute the
index — and a Lean definition for a given index — with `Semantics/Example/frame_index.py`,
which documents the encoding.

**A comparison of two logics lives in the stronger logic's module.** A strict-inclusion lemma such as `LogicE_ssubset_LogicEM : @LogicE ℕ ⊂ LogicEM` belongs in `Logic/EM.lean`, not in `Logic/E.lean`: the module of a logic collects everything that ends at that logic, so its inclusions from below are part of its own story, and the weaker logic's module stays independent of the logics extending it. Incomparability of two logics needs no module of its own: it is the conjunction of the two `not_provable_*` lemmas below, each already stated in the module of the logic it is about.

**But what a single logic fails to prove lives in that logic's own module**, as a statement about that logic alone: `LogicE.not_provable_axiomFour : ∃ A, Axioms.Four A ∉ @LogicE α` belongs in `Logic/E.lean`, next to `LogicE.sound`, since it is a fact about `LogicE` and mentions no other logic. The strict inclusion `LogicE_ssubset_LogicE4` in `Logic/E4.lean` then just invokes it, instead of re-running the countermodel argument itself.

**Everything a per-logic module says about its own logic goes in a `namespace Logic<X>`.** `Logic/E.lean` declares `LogicE.sound`, `LogicE.complete`, the `(@LogicE α).IsConsistent` instance and `LogicE.not_provable_axiomFour` inside `namespace LogicE`, written without the `LogicE.` prefix. Only the comparisons with other logics (`LogicE_ssubset_LogicE4`) stay at the root, since they belong to no single logic's namespace.

## Instantiating implicit type arguments

When a definition's implicit type argument is determined by the surrounding statement — e.g. `A ∈ LogicE` with `A : Formula α` already fixing `α` — write it with no annotation at all. When it genuinely needs pinning (typically a standalone `instance : (@LogicE α).IsConsistent` or a concrete `@LogicE ℕ` in a comparison), use the `@`-application form `@LogicE α`, not the named-argument form `LogicE (α := α)`.

## Comments and docstrings

**Do not write docstrings that merely restate the declaration**, e.g. `/-- LogicEB is sound with respect to every symmetric neighborhood frame. -/` on `LogicEB.sound`, nor `/-! ### ... -/` section headers inside the small per-logic modules — the statements are self-describing and the headers just add noise. A module docstring at the top of the file, and docstrings that carry information the statement cannot (a countermodel's intent, a literature reference), are still welcome.

All comments and docstrings are written in English.

🤖 Keep comments minimal. A docstring explains only what the statement says — not the proof strategy. Do not annotate individual `have`s with comments restating them. A sketch of the argument, or an inline comment on the tactic it concerns, is justified only where it is worth keeping for the sake of *other* proofs; an ordinary inline comment is justified only for what the code cannot express (an elaboration pitfall, why a natural alternative fails), in about one line.

🤖 When refactoring, revise docstrings that still explain the proof strategy (how the induction is run, which lemma dispatches which case): keep the description of the statement and the citations, move the parts worth keeping to an inline comment just before the tactic they concern, and delete the rest. Lemma names mentioned in comments and docstrings must follow renames.

### References and citations

When a definition or theorem formalizes a result from the literature, add the source to [references.bib](../references.bib) (formatted with bibtool, see [references.md](./references.md)) and cite it in the docstring, so a reader can find the informal counterpart.

Citations go at the end of the docstring as a list, one line per BibTeX key, of the form `- [key, kind number]` — even for a single citation. Do not embed them in running text, write out author names, years, titles or journals, or write `**Corollary 41(i) in [Lit04]**:`. Several results from the same key stay on one line:

```
- [Lit04, Corollary 42]
- [Fin74, Theorem 10, Theorem 11(b), Theorem 11(c)]
```

A year or an author name found in a source counts as a citation to look up: search `references.bib` for the matching key. Where no entry exists, leave the historical mention as plain text without brackets.

🤖 A claim about *attribution* — that a technique, proposition or definition does or does not appear in a particular paper — is never written from memory. Read the relevant pages of the source first. Formulations that look different often exist in both papers, so check in the body of each which part is really specific to which source.

### Stale comments and planning artifacts

🤖 Code and docstrings must not reference development-time artifacts: plan steps ("see plan Step4 §3"), issue numbers, bare step numbers, section/line labels (`§2`, `L4-1`), or the implementation state of another file ("even while Step 2 is incomplete …"). They are fine as working memos — the plan they refer to is invisible to a reviewer — but before submission, remove them or rewrite them into self-contained explanations. `grep -n "see plan\|issue #\|Step [0-9]\|§[0-9]\|L[0-9]-[0-9]"` helps find survivors.

🤖 Likewise remove skeleton-era comments (e.g. "most lemmas below are stated with `sorry`") that contradict the finished code.

## The `grind` tactic

Attach `@[grind]` to lemmas and definitions that plausibly help `grind` close goals, and try `grind` inside proofs before settling on a longer tactic sequence.

**A bare `@[grind]` without a direction is not allowed.** Always state one — `@[grind .]`, `@[grind =]`, `@[grind =>]`, `@[grind →]`, `@[grind <=]` — including on recursive `def`s. When `grind` suggests an attribute in an error or hint message, that suggestion is a reasonable choice. The post-hoc form `attribute [grind =] name₁ name₂ …` is equally acceptable.

## No `sorry`

`sorry` is never acceptable in a submitted proof: `lake build` reports it as a warning, and the pre-submission checks in [index.md](./index.md) require a warning-free build. If a proof is incomplete, keep it out of the PR rather than submitting it with `sorry` placeholders.

## `set_option`

Whenever you use `set_option` (including the single-declaration form `set_option foo false in`), add a comment explaining the intent: which option is changed, why, and for which declaration. The comment must make clear to a later reader that the option change is deliberate, not a workaround left behind by accident.

**`set_option maxHeartbeats` must not be used actively.** 🤖 In particular, do not raise it to push a proof through — needing it is a sign that the proof is in an inefficient form. If a proof only works that way, refactor until the option is unnecessary: extract lemmas, narrow the `grind`/`simp` sets, avoid computationally heavy definitions.
