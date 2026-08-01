module

public import Neighborhood.Logic.Logic.ED45
public import Neighborhood.Logic.Logic.EC45
public import Neighborhood.Logic.Logic.ECD5
public import Neighborhood.Logic.Logic.ECD4
public import Neighborhood.Semantics.Example.Frame2_90
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_8553090

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECD45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial] [F.IsTransitive]
    [F.IsEuclidean] :
    A ∈ LogicECD45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECD45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECD45.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECD45 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomK hab (LogicECD45.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECD45 α) := by
  by_contra! hcon
  exact frame_2_90.not_valid_axiomM hab (LogicECD45.sound frame_2_90 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECD45 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomN (LogicECD45.sound frame_2_90 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECD45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicECD45.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECD45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicECD45.sound frame_2_170 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECD45 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomP (LogicECD45.sound frame_2_90 hcon)

theorem ssubset_LogicEC45 : @LogicEC45 ℕ ⊂ LogicECD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEC45.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicECD4 : @LogicECD4 ℕ ⊂ LogicECD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECD4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicECD5 : @LogicECD5 ℕ ⊂ LogicECD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECD5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicED45 : @LogicED45 ℕ ⊂ LogicECD45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicED45.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, ProvableHilbert.axm (by grind), hA⟩

end LogicECD45

end
