module

public import Neighborhood.Logic.Logic.EB4
public import Neighborhood.Logic.Logic.EB5
public import Neighborhood.Logic.Logic.E45
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_11570344

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEB45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSymmetric] [F.IsTransitive]
    [F.IsEuclidean] :
    A ∈ LogicEB45 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEB45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEB45.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEB45 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicEB45.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEB45 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicEB45.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEB45 α) := by
  by_contra! hcon
  exact frame_3_11570344.not_valid_axiomC hab (LogicEB45.sound frame_3_11570344 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEB45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEB45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEB45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEB45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEB45 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEB45.sound frame_1_3 hcon)

theorem ssubset_LogicE45 : @LogicE45 ℕ ⊂ LogicEB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicE45.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicEB4 : @LogicEB4 ℕ ⊂ LogicEB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEB4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicEB5 : @LogicEB5 ℕ ⊂ LogicEB45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEB5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, ProvableHilbert.axm (by grind), hA⟩

end LogicEB45

end
