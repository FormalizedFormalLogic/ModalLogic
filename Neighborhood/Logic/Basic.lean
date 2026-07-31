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

/-- `L` does not prove `⊥`. A class, so that the consistency of a concrete logic is registered
once and picked up by instance search wherever it is needed (notably to produce a maximal
consistent set of `L`). -/
class Logic.IsConsistent (L : Logic α) : Prop where
  not_provable_falsum : ⊥ ∉ L

abbrev Logic.IsTrivial (L : Logic α) : Prop := L = Set.univ

end
