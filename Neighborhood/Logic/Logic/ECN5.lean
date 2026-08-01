module

public import Neighborhood.Logic.Logic.ECN
public import Neighborhood.Logic.Logic.EC5
public import Neighborhood.Logic.Logic.EN5
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_153
public import Neighborhood.Semantics.Example.Frame2_170

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECN5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsRegular] [F.IsEuclidean]
  : A ∈ LogicECN5 → F ⊧ A := Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECN5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECN5.sound frame_1_2 hC⟩

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECN5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECN5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECN5 α) := by
  by_contra! hcon
  exact frame_2_186.not_valid_axiomFour
    (LogicECN5.sound frame_2_186 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECN5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicECN5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECN5 α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomK hab (LogicECN5.sound frame_2_153 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECN5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECN5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECN5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicECN5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECN5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicECN5.sound frame_1_3 hcon)

theorem ssubset_LogicECN : @LogicECN ℕ ⊂ LogicECN5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicECN.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEC5 : @LogicEC5 ℕ ⊂ LogicECN5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEC5.not_provable_axiomN⟩

theorem ssubset_LogicEN5 : @LogicEN5 ℕ ⊂ LogicECN5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEN5.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicECN5

end
