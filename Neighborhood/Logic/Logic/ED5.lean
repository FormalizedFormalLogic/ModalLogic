module

public import Neighborhood.Logic.Logic.ED
public import Neighborhood.Logic.Logic.E5
public import Neighborhood.Semantics.Example.Frame2_90
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_8553090

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicED5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.IsEuclidean]
  : A ∈ LogicED5 → F ⊧ A := Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicED5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicED5.sound frame_1_2 hC⟩

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicED5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomC hab (LogicED5.sound frame_3_10528928 (hcon #a #b))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicED5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomFour (LogicED5.sound frame_3_10528928 (hcon #a))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicED5 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomN (LogicED5.sound frame_2_90 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicED5 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomK hab (LogicED5.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicED5 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicED5.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicED5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicED5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicED5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicED5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicED5 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomP (LogicED5.sound frame_2_90 hcon)

theorem ssubset_LogicED : @LogicED ℕ ⊂ LogicED5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicED.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicE5 : @LogicE5 ℕ ⊂ LogicED5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, hA⟩ := LogicE5.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicED5

end
