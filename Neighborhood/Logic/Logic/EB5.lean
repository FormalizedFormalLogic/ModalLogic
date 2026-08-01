module

public import Neighborhood.Logic.Logic.EB
public import Neighborhood.Logic.Logic.E5
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_79
public import Neighborhood.Semantics.Example.Frame2_95
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_11570344

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEB5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSymmetric] [F.IsEuclidean] :
    A ∈ LogicEB5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEB5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEB5.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEB5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicEB5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEB5 α) := by
  by_contra! hcon
  exact frame_2_79.not_valid_axiomM hab (LogicEB5.sound frame_2_79 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEB5 α) := by
  by_contra! hcon
  exact frame_3_11570344.not_valid_axiomC hab (LogicEB5.sound frame_3_11570344 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEB5 α) := by
  intro hcon
  exact frame_2_95.not_valid_axiomN (LogicEB5.sound frame_2_95 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEB5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEB5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEB5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEB5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEB5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEB5.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEB5 α) := by
  by_contra! hcon
  exact frame_2_79.not_valid_axiomFour (LogicEB5.sound frame_2_79 (hcon #a))

theorem ssubset_LogicE5 : @LogicE5 ℕ ⊂ LogicEB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicE5.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicEB : @LogicEB ℕ ⊂ LogicEB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEB.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, ProvableHilbert.axm (by grind), hA⟩

end LogicEB5

end
