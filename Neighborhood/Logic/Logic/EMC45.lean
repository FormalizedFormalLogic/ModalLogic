module

public import Neighborhood.Logic.Logic.EMCN4
public import Neighborhood.Logic.Logic.EMC5

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

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMC45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEMC45.sound frame_2_170 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMC45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMC45.sound frame_1_3 (hcon #a))

end LogicEMC45

theorem LogicEMC45.ssubset_LogicEMCN4 : @LogicEMCN4 ℕ ⊂ LogicEMC45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomFour
  · obtain ⟨A, hA⟩ := LogicEMCN4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMC45.ssubset_LogicEMC5 : @LogicEMC5 ℕ ⊂ LogicEMC45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMC5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

end
