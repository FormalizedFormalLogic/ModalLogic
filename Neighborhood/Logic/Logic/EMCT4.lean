module

public import Neighborhood.Logic.Logic.EMT4
public import Neighborhood.Logic.Logic.EMC4
public import Neighborhood.Semantics.Example.Frame1_0

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCT4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsReflexive] [F.IsTransitive] :
    A ∈ LogicEMCT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCT4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCT4.sound frame_1_2 hC⟩

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMCT4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMCT4.sound frame_1_0 hcon)

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMCT4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMCT4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCT4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMCT4.sound frame_1_0 (hcon #a))

theorem ssubset_LogicEMT4 : @LogicEMT4 ℕ ⊂ LogicEMCT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEMT4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMCT4

end
