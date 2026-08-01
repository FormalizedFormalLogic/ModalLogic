module

public import Neighborhood.Logic.Logic.EMCND
public import Neighborhood.Logic.Logic.EMB
public import Neighborhood.Logic.Logic.EDB
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMDB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSerial]
    [F.IsSymmetric] :
    A ∈ LogicEMDB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMDB.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEMDB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEMDB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEMDB.sound frame_2_140 (hcon #a))

theorem ssubset_LogicEMCND : @LogicEMCND ℕ ⊂ LogicEMDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMCND.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMB : @LogicEMB ℕ ⊂ LogicEMDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMB.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEDB : @LogicEDB ℕ ⊂ LogicEMDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEDB.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMDB

end
