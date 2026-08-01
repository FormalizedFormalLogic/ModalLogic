module

public import Neighborhood.Logic.Logic.EMCN4
public import Neighborhood.Logic.Logic.EMC5
public import Neighborhood.Logic.Logic.EC45
public import Neighborhood.Logic.Logic.EM45
public import Neighborhood.Semantics.Example.Frame1_3

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMC45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicEMC45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMC45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMC45.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMC45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMC45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMC45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEMC45.sound frame_2_170 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMC45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMC45.sound frame_1_3 (hcon #a))

theorem ssubset_LogicEMCN4 : @LogicEMCN4 ℕ ⊂ LogicEMC45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMCN4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMC5 : @LogicEMC5 ℕ ⊂ LogicEMC45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMC5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEM45 : @LogicEM45 ℕ ⊂ LogicEMC45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEM45.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMC45

end
