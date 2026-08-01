module

public import Neighborhood.Logic.Logic.ECD
public import Neighborhood.Logic.Logic.EC4
public import Neighborhood.Logic.Logic.ED4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_90
public import Neighborhood.Semantics.Example.Frame3_8553090

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECD4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial]
    [F.IsTransitive] :
    A ∈ LogicECD4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECD4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECD4.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECD4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicECD4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECD4 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomK hab (LogicECD4.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECD4 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicECD4.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECD4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicECD4.sound frame_1_0 hcon)

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECD4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicECD4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECD4 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomP (LogicECD4.sound frame_2_90 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECD4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicECD4.sound frame_1_0 (hcon #a))

end LogicECD4

theorem LogicECD4.ssubset_LogicECD : @LogicECD ℕ ⊂ LogicECD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicECD.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECD4.ssubset_LogicEC4 : @LogicEC4 ℕ ⊂ LogicECD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEC4.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECD4.ssubset_LogicED4 : @LogicED4 ℕ ⊂ LogicECD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicED4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
