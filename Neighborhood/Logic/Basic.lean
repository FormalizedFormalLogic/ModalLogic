module

public import Neighborhood.Formula.Basic

/-!
# Logics

A logic is a set of formulas, regarded as the set of its theorems. Provability of `A` in `L` is
membership `A ∈ L`, and comparison of logics is inclusion of the underlying sets.
-/

@[expose] public section

variable {α : Type u}

/-- A logic, i.e. a set of formulas regarded as the set of its theorems. -/
abbrev Logic (α : Type u) := Set (Formula α)

/-- `⊥` is not a theorem of `L`. -/
class Logic.Consistent (L : Logic α) : Prop where
  not_mem_falsum : ⊥ ∉ L

namespace Logic

variable {L : Logic α}

@[simp, grind .]
lemma not_mem_falsum [L.Consistent] : (⊥ : Formula α) ∉ L := Consistent.not_mem_falsum

end Logic

end
