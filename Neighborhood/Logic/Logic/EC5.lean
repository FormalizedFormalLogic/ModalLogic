module

public import Neighborhood.Logic.Logic.EC
public import Neighborhood.Logic.Logic.E5
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_153
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame2_75

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEC5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsEuclidean] :
    A ∈ LogicEC5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEC5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEC5.sound frame_1_2 hC⟩

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEC5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEC5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEC5 α) := by
  by_contra! hcon
  exact frame_2_79.not_valid_axiomFour (LogicEC5.sound frame_2_79 (hcon #a))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEC5 α) := by
  intro hcon
  exact frame_2_75.not_valid_axiomN (LogicEC5.sound frame_2_75 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEC5 α) := by
  by_contra! hcon
  exact frame_2_75.not_valid_axiomK hab (LogicEC5.sound frame_2_75 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEC5 α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomM hab (LogicEC5.sound frame_2_153 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEC5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEC5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEC5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEC5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEC5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEC5.sound frame_1_3 hcon)

theorem ssubset_LogicEC : (@LogicEC ℕ) ⊂ LogicEC5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEC.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicE5 : (@LogicE5 ℕ) ⊂ LogicEC5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicE5.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEC5

end
