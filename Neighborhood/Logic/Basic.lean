module

public import Neighborhood.Formula.Basic

/-!
# Logics

A logic is a set of formulas, regarded as the set of its theorems. Provability of `φ` in `L` is
membership `φ ∈ L`, and comparison of logics is inclusion of the underlying sets.
-/

@[expose] public section

/-- A logic, i.e. a set of formulas regarded as the set of its theorems. -/
abbrev Logic := Set Formula

/-- `⊥` is not a theorem of `L`. -/
class Logic.Consistent (L : Logic) : Prop where
  not_mem_falsum : ⊥ ∉ L

namespace Logic

variable {L : Logic}

@[simp, grind .]
lemma not_mem_falsum [L.Consistent] : (⊥ : Formula) ∉ L := Consistent.not_mem_falsum

end Logic

end
