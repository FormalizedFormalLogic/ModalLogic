module

public import Neighborhood.Logic.Logic.EM4
public import Neighborhood.Logic.Logic.ED4
public import Neighborhood.Logic.Logic.EMD
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame3_43176

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMD4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsTransitive] [F.IsSerial] :
    A ∈ LogicEMD4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMD4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMD4.sound frame_1_2 hC⟩

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMD4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMD4.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMD4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEMD4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMD4 α) := by
  by_contra! hcon
  exact frame_3_43176.not_valid_axiomK hab (LogicEMD4.sound frame_3_43176 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMD4 α) := by
  by_contra! hcon
  exact frame_3_43176.not_valid_axiomC hab (LogicEMD4.sound frame_3_43176 (hcon #a #b))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMD4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMD4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMD4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMD4.sound frame_1_0 (hcon #a))

end LogicEMD4

theorem LogicEMD4.ssubset_LogicEM4 : @LogicEM4 ℕ ⊂ LogicEMD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEM4.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMD4.ssubset_LogicED4 : @LogicED4 ℕ ⊂ LogicEMD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicED4.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMD4.ssubset_LogicEMD : @LogicEMD ℕ ⊂ LogicEMD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEMD.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

end
