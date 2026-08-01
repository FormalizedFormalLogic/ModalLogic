module

public import Neighborhood.Logic.Logic.EMCN
public import Neighborhood.Logic.Logic.EMCD
public import Neighborhood.Logic.Logic.ECND

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCND

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.ContainsUnit] [F.IsSerial] :
    A ∈ LogicEMCND → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCND α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCND.sound frame_1_2 hC⟩

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMCND α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEMCND.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEMCND.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMCND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEMCND.sound frame_2_140 (hcon #a))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMCND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEMCND.sound frame_2_140 (hcon #a))

theorem ssubset_LogicEMCN : @LogicEMCN ℕ ⊂ LogicEMCND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMCN.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMCD : @LogicEMCD ℕ ⊂ LogicEMCND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEMCD.not_provable_axiomN⟩

theorem ssubset_LogicECND : @LogicECND ℕ ⊂ LogicEMCND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicECND.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

/-- Over `EMCN` (i.e. over the normal base `K`), the axiom `P` and the axiom scheme `D`
axiomatise the same logic. -/
theorem eq_LogicEMCNP : (@LogicEMCND α) = LogicEMCNP := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨B, C, rfl⟩ | ⟨B, C, rfl⟩) | rfl) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN |
        exact Logic.axiomP_of_ND

end LogicEMCND

end
