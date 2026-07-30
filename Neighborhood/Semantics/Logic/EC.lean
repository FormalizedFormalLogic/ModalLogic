module

public import Neighborhood.Semantics.Logic.E
import Neighborhood.Semantics.Example.Frame1_2
import Neighborhood.Semantics.Example.Frame2_22

/-!
# The neighborhood logic `LogicEC`

Soundness, consistency and completeness of `LogicEC`, the classical modal logic axiomatised by
the regularity axiom `C`, with respect to the regular neighborhood frames, and its strict
inclusion in `LogicE`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEC.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] :
    A ∈ LogicEC → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, _, rfl⟩; simp)

theorem LogicEC.consistent : (@LogicEC α).IsConsistent := by
  by_contra! hC
  simpa using LogicEC.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEC α)) :=
  MaximalConsistentSet.nonempty LogicEC.consistent

variable [DecidableEq α]

theorem LogicEC.complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsRegular] → F ⊧ A) :
    A ∈ @LogicEC α :=
  (basicCanonicity LogicEC).mem_of_valid
    (h (basicCanonicity LogicEC).toModel.toFrame
      (basicCanonicity LogicEC).toModel.Val)


theorem LogicE_ssubset_LogicEC : (@LogicE ℕ) ⊂ LogicEC := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hC : Axioms.C #0 #1 ∈ (@LogicE ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_22.not_valid_axiomC (LogicE.sound _ hC)

end
