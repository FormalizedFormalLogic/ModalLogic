module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Logic.EMN
public import Neighborhood.Semantics.Logic.EMP
public import Neighborhood.Semantics.Logic.ENP
public import Neighborhood.Semantics.Supplementation
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_9471106

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMNP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.ContainsUnit]
    [F.NotContainsEmpty] :
    A ∈ LogicEMNP → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | rfl) <;> simp)

instance : (@LogicEMNP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMNP.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] →
      [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicEMNP α :=
  (supplementedBasicCanonicalModel LogicEMNP).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMNP).toFrame
      (supplementedBasicCanonicalModel LogicEMNP).Val)

end LogicEMNP

theorem LogicEMP_ssubset_LogicEMNP : @LogicEMP ℕ ⊂ LogicEMNP := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by rintro A (⟨B, C, rfl⟩ | rfl) <;> grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEMP ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicEMP.sound frame_1_0 hN)

theorem LogicEMN_ssubset_LogicEMNP : @LogicEMN ℕ ⊂ LogicEMNP := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hP : (Axioms.P : Formula ℕ) ∈ @LogicEMN ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomP (LogicEMN.sound frame_1_3 hP)

theorem LogicENP_ssubset_LogicEMNP : @LogicENP ℕ ⊂ LogicEMNP := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.union_subset_union_left _ Set.subset_union_right)
  · intro h
    have hM : Axioms.M #0 #1 ∈ @LogicENP ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_9471106.not_valid_axiomM (LogicENP.sound frame_3_9471106 hM)

end
