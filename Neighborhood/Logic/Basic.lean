module

public import Neighborhood.Formula.Basic

/-!
# Logics

A logic is a set of formulas, regarded as the set of its theorems. Provability of `A` in `L` is
membership `A ∈ L`, and comparison of logics is inclusion of the underlying sets.
-/

@[expose] public section

variable {α : Type u}

abbrev Logic (α : Type u) := Set (Formula α)

abbrev Logic.IsConsistent (L : Logic α) : Prop := ⊥ ∉ L
abbrev Logic.IsTrivial (L : Logic α) : Prop := L = Set.univ

end
