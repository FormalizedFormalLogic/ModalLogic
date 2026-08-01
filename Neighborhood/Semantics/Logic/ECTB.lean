module

public import Neighborhood.Semantics.Logic.ETB
public import Neighborhood.Semantics.Logic.ECNDB
public import Neighborhood.Semantics.Logic.ECNT
public import Neighborhood.Semantics.Example.Frame3_8437920
public import Neighborhood.Semantics.Example.Frame3_9472136

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECTB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsReflexive]
    [F.IsSymmetric] :
    A ∈ LogicECTB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECTB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECTB.sound frame_1_2 hC⟩

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECTB α) := by
  by_contra! hcon
  exact frame_3_8437920.not_valid_axiomFive (LogicECTB.sound frame_3_8437920 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECTB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicECTB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECTB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicECTB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECTB α) := by
  by_contra! hcon
  exact frame_3_8437920.not_valid_axiomFour (LogicECTB.sound frame_3_8437920 (hcon #a))

end LogicECTB

theorem LogicETB_ssubset_LogicECTB : @LogicETB ℕ ⊂ LogicECTB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicETB.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECNDB_ssubset_LogicECTB : @LogicECNDB ℕ ⊂ LogicECTB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomB
  · obtain ⟨A, hA⟩ := LogicECNDB.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECNT_ssubset_LogicECTB : @LogicECNT ℕ ⊂ LogicECTB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT
  · obtain ⟨A, hA⟩ := LogicECNT.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

end
