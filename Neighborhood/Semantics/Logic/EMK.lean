module

public import Neighborhood.Semantics.Logic.EK
public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Logic.Equiv.EMK_EMCK
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_8

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMK

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.HasPropertyK] :
    A ∈ LogicEMK → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp)

instance : (@LogicEMK α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMK.sound frame_1_2 hC⟩

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMK α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMK.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMK α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMK.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMK α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMK.sound frame_1_0 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMK α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMK.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMK α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMK.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMK α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEMK.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMK α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMK.sound frame_1_0 (hcon #a))

end LogicEMK

theorem LogicEK_ssubset_LogicEMK : @LogicEK ℕ ⊂ LogicEMK := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicEK.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEM_ssubset_LogicEMK : @LogicEM ℕ ⊂ LogicEMK := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, B, hA⟩ := LogicEM.not_provable_axiomK (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.K A B, (ProvableHilbert.axm (by grind)), hA⟩

end
