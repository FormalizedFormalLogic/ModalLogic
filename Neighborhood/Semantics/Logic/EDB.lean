module

public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.EB
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_3346281

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEDB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.IsSymmetric]
  : A ∈ LogicEDB → F ⊧ A := Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEDB.sound frame_1_1 hC⟩

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEDB α) := by
  by_contra! hcon
  exact frame_3_3346281.not_valid_axiomC hab (LogicEDB.sound frame_3_3346281 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEDB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomN (LogicEDB.sound frame_1_1 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEDB α) := by
  by_contra! hcon
  exact frame_3_3346281.not_valid_axiomK hab (LogicEDB.sound frame_3_3346281 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEDB α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomM hab (LogicEDB.sound frame_1_1 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEDB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEDB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicEDB.sound frame_1_1 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEDB α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicEDB.sound frame_1_1 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEDB.sound frame_2_140 (hcon #a))

end LogicEDB


theorem LogicED_ssubset_LogicEDB : @LogicED ℕ ⊂ LogicEDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicED.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEB_ssubset_LogicEDB : @LogicEB ℕ ⊂ LogicEDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, hA⟩ := LogicEB.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
