module

public import Neighborhood.Logic.Logic.EMCND4
public import Neighborhood.Logic.Logic.EMCNT
public import Neighborhood.Logic.Logic.ECNT4
public import Neighborhood.Logic.Logic.EMCT4
public import Neighborhood.Logic.Logic.EMNT4

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

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMCNT4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEMCNT4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCNT4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEMCNT4.sound frame_2_138 (hcon #a))

theorem ssubset_LogicEMCND4 : @LogicEMCND4 ℕ ⊂ LogicEMCNT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMCND4.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMCNT : @LogicEMCNT ℕ ⊂ LogicEMCNT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMCNT.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECNT4 : @LogicECNT4 ℕ ⊂ LogicEMCNT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicECNT4.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicEMCT4 : @LogicEMCT4 ℕ ⊂ LogicEMCNT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · have hA := LogicEMCT4.not_provable_axiomN (α := ℕ)
    exact ⟨Axioms.N, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicEMNT4 : @LogicEMNT4 ℕ ⊂ LogicEMCNT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEMNT4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMCNT4

end
