module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Logic.ECD
public import Neighborhood.Semantics.Example.Frame1_1

/-!
# The neighborhood logic `LogicECP`

Soundness, consistency and completeness of `LogicECP`, the classical modal logic axiomatised by
both the regularity axiom `C` and the possibility axiom `P` over `LogicE`, with respect to the
regular neighborhood frames in which no world has the empty set as one of its neighborhoods.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicECP.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.NotContainsEmpty] :
    A ∈ LogicECP → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

theorem LogicECP.consistent : (@LogicECP α).IsConsistent := by
  by_contra! hC
  simpa using LogicECP.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECP α)) :=
  MaximalConsistentSet.nonempty LogicECP.consistent

variable [DecidableEq α]

theorem LogicECP.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsRegular] → [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicECP α :=
  (basicCanonicity LogicECP).mem_of_valid
    (h (basicCanonicity LogicECP).toModel.toFrame
      (basicCanonicity LogicECP).toModel.Val)

theorem LogicECD_ssubset_LogicECP : @LogicECD ℕ ⊂ LogicECP := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, C, rfl⟩ | ⟨B, rfl⟩) <;> first | exact Logic.axiomC | exact Logic.axiomD
  · intro h
    have hP : (Axioms.P : Formula ℕ) ∈ @LogicECD ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_1.not_valid_axiomP (LogicECD.sound frame_1_1 hP)

end
