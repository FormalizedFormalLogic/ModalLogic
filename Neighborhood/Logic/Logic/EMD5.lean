module

public import Neighborhood.Logic.Logic.END5
public import Neighborhood.Logic.Logic.EMND
public import Neighborhood.Logic.Logic.EM5
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_10528928

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMD5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSerial] [F.IsEuclidean] :
    A ∈ LogicEMD5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMD5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMD5.sound frame_1_2 hC⟩

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMD5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomFour (LogicEMD5.sound frame_3_10528928 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMD5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomK hab (LogicEMD5.sound frame_3_10528928 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMD5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomC hab (LogicEMD5.sound frame_3_10528928 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMD5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEMD5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMD5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEMD5.sound frame_2_170 (hcon #a))

theorem ssubset_LogicEND5 : @LogicEND5 ℕ ⊂ LogicEMD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEND5.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMND : @LogicEMND ℕ ⊂ LogicEMD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMND.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEM5 : @LogicEM5 ℕ ⊂ LogicEMD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEM5.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMD5

end
