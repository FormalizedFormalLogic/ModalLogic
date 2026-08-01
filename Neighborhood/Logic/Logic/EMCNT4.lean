module

public import Neighborhood.Logic.Logic.EMCND4
public import Neighborhood.Logic.Logic.EMCNT

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCNT4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.ContainsUnit] [F.IsReflexive] [F.IsTransitive] :
    A ∈ LogicEMCNT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCNT4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCNT4.sound frame_1_2 hC⟩

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCNT4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEMCNT4.sound frame_2_138 (hcon #a))

end LogicEMCNT4

theorem LogicEMCNT4.ssubset_LogicEMCND4 : @LogicEMCND4 ℕ ⊂ LogicEMCNT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD |
        exact Logic.axiomFour
  · obtain ⟨A, hA⟩ := LogicEMCND4.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMCNT4.ssubset_LogicEMCNT : @LogicEMCNT ℕ ⊂ LogicEMCNT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMCNT.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

end
