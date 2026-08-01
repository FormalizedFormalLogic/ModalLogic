module

public import Neighborhood.Logic.Logic.EMT
public import Neighborhood.Logic.Logic.ECT
public import Neighborhood.Logic.Logic.EMCD
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_8

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsReflexive] :
    A ∈ LogicEMCT → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCT.sound frame_1_2 hC⟩

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMCT α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMCT.sound frame_1_0 hcon)

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMCT α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMCT.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMCT α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEMCT.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCT α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMCT.sound frame_1_0 (hcon #a))

theorem ssubset_LogicEMT : @LogicEMT ℕ ⊂ LogicEMCT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEMT.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECT : @LogicECT ℕ ⊂ LogicEMCT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicECT.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMCD : @LogicEMCD ℕ ⊂ LogicEMCT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMCD.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMCT

end
