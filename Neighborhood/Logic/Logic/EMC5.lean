module

public import Neighborhood.Logic.Logic.EMCN
public import Neighborhood.Logic.Logic.EM5
public import Neighborhood.Logic.Logic.ECN5
public import Neighborhood.Semantics.Example.Frame3_10529440
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_170

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMC5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsEuclidean] :
    A ∈ LogicEMC5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMC5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMC5.sound frame_1_2 hC⟩

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMC5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMC5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMC5 α) := by
  by_contra! hcon
  exact frame_3_10529440.not_valid_axiomFour (LogicEMC5.sound frame_3_10529440 (hcon #a))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMC5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMC5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMC5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEMC5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMC5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMC5.sound frame_1_3 hcon)

theorem ssubset_LogicEMCN : @LogicEMCN ℕ ⊂ LogicEMC5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN
  · obtain ⟨A, hA⟩ := LogicEMCN.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEM5 : @LogicEM5 ℕ ⊂ LogicEMC5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEM5.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECN5 : @LogicECN5 ℕ ⊂ LogicEMC5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomN
    · exact Logic.axiomFive
  · obtain ⟨A, B, hA⟩ := LogicECN5.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMC5

end
