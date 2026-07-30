module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Supplementation

/-!
# The neighborhood logic `LogicEMP`

Soundness, consistency and completeness of `LogicEMP`, the classical modal logic axiomatised by
both the monotonicity axiom `M` and the possibility axiom `P` over `LogicE`, with respect to the
monotonic neighborhood frames in which no world has the empty set as one of its neighborhoods.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMP.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.NotContainsEmpty] :
    A ∈ LogicEMP → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

theorem LogicEMP.consistent : (@LogicEMP α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMP.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMP α)) :=
  MaximalConsistentSet.nonempty LogicEMP.consistent

variable [DecidableEq α]

theorem LogicEMP.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicEMP α :=
  (supplementedBasicCanonicity LogicEMP).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMP).toModel.toFrame
      (supplementedBasicCanonicity LogicEMP).toModel.Val)

end
