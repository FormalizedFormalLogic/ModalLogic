module

public import Neighborhood.Semantics.Logic.E

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicECD.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial] :
    A ∈ LogicECD → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

theorem LogicECD.consistent : (@LogicECD α).IsConsistent := by
  by_contra! hC
  simpa using LogicECD.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECD α)) :=
  MaximalConsistentSet.nonempty LogicECD.consistent

variable [DecidableEq α]

theorem LogicECD.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsRegular] → [F.IsSerial] → F ⊧ A) :
    A ∈ @LogicECD α :=
  (basicCanonicity LogicECD).mem_of_valid
    (h (basicCanonicity LogicECD).toModel.toFrame
      (basicCanonicity LogicECD).toModel.Val)

end
