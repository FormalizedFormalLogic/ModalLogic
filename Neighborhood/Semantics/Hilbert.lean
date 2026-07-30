module

public import Neighborhood.Hilbert.Basic
public import Neighborhood.Semantics.Basic

/-!
# Soundness of Hilbert-style neighborhood calculi

Soundness of `Hilbert Ax` with respect to any frame validating every axiom of `Ax`: every
formula provable from `Ax` is valid on `F` as soon as `F` validates every member of `Ax`.
-/

@[expose] public section

variable {α : Type u} {κ : Type v} [Nonempty κ]
variable {Ax : FormulaSet α} {A : Formula α} {F : Frame κ}

namespace Hilbert

/-- `Hilbert Ax` is sound with respect to any frame `F` validating every axiom of `Ax`. -/
theorem sound (hAx : ∀ B ∈ Ax, F ⊧ B) : A ∈ Hilbert Ax → F ⊧ A := by
  intro hA
  induction hA using ProvableHilbert.rec with
  | axm hmem => exact hAx _ hmem
  | mdp _ _ ih₁ ih₂ => exact ih₁.mdp ih₂
  | re _ ih => exact ih.re
  | implyK A B => intro V x; grind
  | implyS A B C => intro V x; grind
  | dne A => intro V x; grind
  | andElim₁ A B => intro V x; grind
  | andElim₂ A B => intro V x; grind
  | andIntro A B => intro V x; grind
  | orIntro₁ A B => intro V x; grind
  | orIntro₂ A B => intro V x; grind
  | orElim A B C => intro V x; grind

end Hilbert

end
