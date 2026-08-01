module

public import Neighborhood.Logic.Logic.ECND4
public import Neighborhood.Logic.Logic.ECND5
public import Neighborhood.Logic.Logic.ECN45
public import Neighborhood.Logic.Logic.ECD45
public import Neighborhood.Logic.Logic.END45
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_8553090

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECND45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] [F.IsSerial] [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicECND45 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECND45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECND45.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECND45 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomK hab (LogicECND45.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECND45 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicECND45.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECND45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicECND45.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECND45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicECND45.sound frame_2_170 (hcon #a))

theorem ssubset_LogicECD45 : @LogicECD45 ℕ ⊂ LogicECND45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · exact ⟨Axioms.N, ProvableHilbert.axm (by grind), LogicECD45.not_provable_axiomN⟩

theorem ssubset_LogicECN45 : @LogicECN45 ℕ ⊂ LogicECND45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECN45.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicECND4 : @LogicECND4 ℕ ⊂ LogicECND45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECND4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicECND5 : @LogicECND5 ℕ ⊂ LogicECND45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECND5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicEND45 : @LogicEND45 ℕ ⊂ LogicECND45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEND45.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, ProvableHilbert.axm (by grind), hA⟩

end LogicECND45

end
