module

public import Neighborhood.Semantics.Logic.EMCN
public import Neighborhood.Semantics.Logic.ECNB
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSymmetric] :
    A ∈ LogicEMB → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMB.sound frame_1_2 hC⟩

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEMB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMB α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMB.sound frame_1_3 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEMB.sound frame_2_140 (hcon #a))

end LogicEMB

theorem LogicEMCN_ssubset_LogicEMB : @LogicEMCN ℕ ⊂ LogicEMB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN
  · obtain ⟨A, hA⟩ := LogicEMCN.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECNB_ssubset_LogicEMB : @LogicECNB ℕ ⊂ LogicEMB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomN
    · exact Logic.axiomB
  · obtain ⟨A, B, hA⟩ := LogicECNB.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
