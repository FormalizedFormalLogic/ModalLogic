module

public import Neighborhood.Logic.Logic.ECN
public import Neighborhood.Logic.Logic.EC4
public import Neighborhood.Logic.Logic.EN4
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_153

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECN4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsRegular] [F.IsTransitive]
  : A ∈ LogicECN4 → F ⊧ A := Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECN4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECN4.sound frame_1_2 hC⟩

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECN4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicECN4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECN4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECN4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECN4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive
    (LogicECN4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECN4 α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomK hab (LogicECN4.sound frame_2_153 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECN4 α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomM hab (LogicECN4.sound frame_2_153 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECN4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECN4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECN4 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicECN4.sound frame_1_3 hcon)

end LogicECN4

theorem LogicECN4.ssubset_LogicECN : @LogicECN ℕ ⊂ LogicECN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicECN.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECN4.ssubset_LogicEC4 : @LogicEC4 ℕ ⊂ LogicECN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEC4.not_provable_axiomN⟩

theorem LogicECN4.ssubset_LogicEN4 : @LogicEN4 ℕ ⊂ LogicECN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEN4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
