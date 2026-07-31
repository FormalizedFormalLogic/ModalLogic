module

public import Neighborhood.Semantics.Logic.ECD
public import Neighborhood.Semantics.Logic.ECB
public import Neighborhood.Semantics.Logic.EDB
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_9472136

/-!
# The neighborhood logic `LogicECDB`

Soundness and consistency of `LogicECDB`, the classical modal logic axiomatised by the regularity
axiom `C`, the seriality axiom `D`, and the symmetry axiom `B`, with respect to the regular,
serial, and symmetric neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECDB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial]
    [F.IsSymmetric] :
    A ∈ LogicECDB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECDB.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECDB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicECDB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECDB α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomM hab (LogicECDB.sound frame_1_1 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECDB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomN (LogicECDB.sound frame_1_1 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicECDB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECDB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicECDB.sound frame_1_1 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECDB α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicECDB.sound frame_1_1 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicECDB.sound frame_2_140 (hcon #a))

end LogicECDB

theorem LogicECD_ssubset_LogicECDB : @LogicECD ℕ ⊂ LogicECDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECD.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECB_ssubset_LogicECDB : @LogicECB ℕ ⊂ LogicECDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECB.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEDB_ssubset_LogicECDB : @LogicEDB ℕ ⊂ LogicECDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEDB.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
