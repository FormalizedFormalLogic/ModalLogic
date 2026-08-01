module

public import Neighborhood.Logic.Logic.ECN
public import Neighborhood.Logic.Logic.ENB
public import Neighborhood.Logic.Logic.ECB
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECNB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsRegular] [F.IsSymmetric]
  : A ∈ LogicECNB → F ⊧ A := Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECNB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECNB.sound frame_1_2 hC⟩

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECNB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECNB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECNB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicECNB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECNB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicECNB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECNB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicECNB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECNB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECNB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECNB α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicECNB.sound frame_1_3 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECNB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicECNB.sound frame_2_140 (hcon #a))

end LogicECNB

theorem LogicECNB.ssubset_LogicECN : @LogicECN ℕ ⊂ LogicECNB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicECN.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECNB.ssubset_LogicENB : @LogicENB ℕ ⊂ LogicECNB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicENB.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECNB.ssubset_LogicECB : @LogicECB ℕ ⊂ LogicECNB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicECB.not_provable_axiomN⟩

end
