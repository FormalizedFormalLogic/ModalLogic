module

public import Neighborhood.Logic.Logic.EMC4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_170

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCD4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.IsTransitive] [F.IsSerial] :
    A ∈ LogicEMCD4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCD4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCD4.sound frame_1_2 hC⟩

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMCD4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMCD4.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMCD4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEMCD4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMCD4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMCD4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCD4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMCD4.sound frame_1_0 (hcon #a))

theorem ssubset_LogicEMC4 : @LogicEMC4 ℕ ⊂ LogicEMCD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMC4.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMCD4

end
