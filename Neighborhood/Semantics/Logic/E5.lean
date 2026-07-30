module

public import Neighborhood.Semantics.Logic.E
import Neighborhood.Semantics.Example.Frame1_2
import Neighborhood.Semantics.Example.Frame3_9471106

/-!
# The neighborhood logic `LogicE5`

Soundness, consistency and completeness of `LogicE5`, the classical modal logic axiomatized by
`Five := ◇A 🡒 □◇A` over `LogicE`, with respect to the euclidean frames (`Frame.IsEuclidean`).
Also its strict inclusion in `LogicE`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicE5.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsEuclidean] :
    A ∈ @LogicE5 α → F ⊧ A :=
  Hilbert.sound (fun B hB => by obtain ⟨B, rfl⟩ := hB; exact valid_axiomFive_of_isEuclidean)

theorem LogicE5.consistent : (@LogicE5 α).IsConsistent := by
  by_contra! hC
  simpa using LogicE5.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicE5 α)) :=
  MaximalConsistentSet.nonempty LogicE5.consistent

variable [DecidableEq α]

theorem LogicE5.complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsEuclidean] → F ⊧ A) :
    A ∈ @LogicE5 α :=
  (maximalRelativeMaximalCanonicity LogicE5).mem_of_valid
    (h (maximalRelativeMaximalCanonicity LogicE5).toModel.toFrame
      (maximalRelativeMaximalCanonicity LogicE5).toModel.Val)


theorem LogicE_ssubset_LogicE5 : @LogicE ℕ ⊂ LogicE5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hFive : Axioms.Five #0 ∈ @LogicE ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_9471106.not_isEuclidean (isEuclidean_of_valid_axiomFive (LogicE.sound _ hFive))

end
