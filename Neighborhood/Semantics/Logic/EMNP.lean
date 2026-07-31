module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Logic.EMP
public import Neighborhood.Semantics.Supplementation
public import Neighborhood.Semantics.Example.Frame1_0

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

theorem LogicEMP_ssubset_LogicEMNP : @LogicEMP ℕ ⊂ LogicEMNP := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by rintro A (⟨B, C, rfl⟩ | rfl) <;> grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEMP ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicEMP.sound frame_1_0 hN)

end
