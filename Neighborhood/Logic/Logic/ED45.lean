module

public import Neighborhood.Logic.Logic.ED4
public import Neighborhood.Logic.Logic.E45
public import Neighborhood.Logic.Logic.ED5
public import Neighborhood.Semantics.Example.Frame2_90
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_8553090
public import Neighborhood.Semantics.Example.Frame3_11053224

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicED45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.IsTransitive]
    [F.IsEuclidean] :
    A ∈ LogicED45 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicED45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicED45.sound frame_1_2 hC⟩

theorem ssubset_LogicED4 : @LogicED4 ℕ ⊂ LogicED45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicED4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicE45 : @LogicE45 ℕ ⊂ LogicED45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicE45.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicED5 : @LogicED5 ℕ ⊂ LogicED45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicED5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicED45 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomK hab (LogicED45.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicED45 α) := by
  by_contra! hcon
  exact frame_2_90.not_valid_axiomM hab (LogicED45.sound frame_2_90 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicED45 α) := by
  by_contra! hcon
  exact frame_3_11053224.not_valid_axiomC hab (LogicED45.sound frame_3_11053224 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicED45 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomN (LogicED45.sound frame_2_90 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicED45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicED45.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicED45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicED45.sound frame_2_170 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicED45 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomP (LogicED45.sound frame_2_90 hcon)

end LogicED45

end
