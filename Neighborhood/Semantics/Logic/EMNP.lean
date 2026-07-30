module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Supplementation

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMNP.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.ContainsUnit]
    [F.NotContainsEmpty] :
    A ∈ LogicEMNP → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | rfl) <;> simp)

theorem LogicEMNP.consistent : (@LogicEMNP α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMNP.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMNP α)) :=
  MaximalConsistentSet.nonempty LogicEMNP.consistent

variable [DecidableEq α]

theorem LogicEMNP.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] →
      [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicEMNP α :=
  (supplementedBasicCanonicity LogicEMNP).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMNP).toModel.toFrame
      (supplementedBasicCanonicity LogicEMNP).toModel.Val)

end
