module

public import Neighborhood.Logic.Logic.E4
public import Neighborhood.Logic.Logic.E5
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_153
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame2_206
public import Neighborhood.Semantics.Example.Frame2_75

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicE45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicE45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicE45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicE45.sound frame_1_2 hC⟩

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicE45 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicE45.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicE45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicE45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicE45 α) := by
  intro hcon
  exact frame_2_75.not_valid_axiomN (LogicE45.sound frame_2_75 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicE45 α) := by
  by_contra! hcon
  exact frame_2_75.not_valid_axiomK hab (LogicE45.sound frame_2_75 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicE45 α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomM hab (LogicE45.sound frame_2_153 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicE45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicE45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicE45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicE45.sound frame_2_170 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicE45 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicE45.sound frame_1_3 hcon)

end LogicE45

theorem LogicE45.ssubset_LogicE4 : @LogicE4 ℕ ⊂ LogicE45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicE4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicE45.ssubset_LogicE5 : @LogicE5 ℕ ⊂ LogicE45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, hA⟩ := LogicE5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

end
