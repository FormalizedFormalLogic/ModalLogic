module

public import Neighborhood.Hilbert.Basic
public import Neighborhood.Semantics.Basic

/-!
# Soundness of Hilbert-style neighborhood calculi

Soundness of `Hilbert Ax` with respect to any frame validating every axiom of `Ax`: every
formula provable from `Ax` is valid on `F` as soon as `F` validates every member of `Ax`. From
this we derive that formulas refuted on `F` are unprovable, and that `Hilbert Ax` is consistent
whenever some frame validates `Ax`.
-/

@[expose] public section

variable {α : Type u} {κ : Type u} [Nonempty κ]
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

/-- A formula refuted on `F` is not provable from an axiom set validated by `F`. -/
theorem not_mem_of_not_valid (hAx : ∀ B ∈ Ax, F ⊧ B) (h : ¬F ⊧ A) : A ∉ Hilbert Ax :=
  fun hA => h (sound hAx hA)

/-- `Hilbert Ax` is consistent whenever some frame validates every axiom of `Ax`. -/
theorem consistent_of (hAx : ∀ B ∈ Ax, F ⊧ B) : (Hilbert Ax).Consistent :=
  ⟨not_mem_of_not_valid hAx (Frame.Validate.not_bot F)⟩

end Hilbert

end
