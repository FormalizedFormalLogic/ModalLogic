module

public import Neighborhood.Logic.Logic.EMDB
public import Neighborhood.Logic.Logic.EMCNT
public import Neighborhood.Logic.Logic.ECTB
public import Neighborhood.Logic.Logic.EMCTB
public import Neighborhood.Semantics.Example.Frame3_8437920

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMTB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsReflexive]
    [F.IsSymmetric] :
    A ∈ LogicEMTB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMTB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMTB.sound frame_1_2 hC⟩

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMTB α) := by
  by_contra! hcon
  exact frame_3_8437920.not_valid_axiomFive (LogicEMTB.sound frame_3_8437920 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMTB α) := by
  by_contra! hcon
  exact frame_3_8437920.not_valid_axiomFour (LogicEMTB.sound frame_3_8437920 (hcon #a))

theorem ssubset_LogicEMDB : @LogicEMDB ℕ ⊂ LogicEMTB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMDB.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMCNT : @LogicEMCNT ℕ ⊂ LogicEMTB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMCNT.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECTB : @LogicECTB ℕ ⊂ LogicEMTB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · rw [← LogicEMCTB.eq_LogicEMTB]
    hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicECTB.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMTB

end
