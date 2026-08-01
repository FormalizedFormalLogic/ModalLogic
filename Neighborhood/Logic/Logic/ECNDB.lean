module

public import Neighborhood.Logic.Logic.ECND
public import Neighborhood.Logic.Logic.ECNB
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_9472136

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECNDB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] [F.IsSerial] [F.IsSymmetric] :
    A ∈ LogicECNDB → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECNDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECNDB.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECNDB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicECNDB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECNDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicECNDB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECNDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicECNDB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECNDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicECNDB.sound frame_2_140 (hcon #a))

theorem ssubset_LogicECND : @LogicECND ℕ ⊂ LogicECNDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECND.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECNB : @LogicECNB ℕ ⊂ LogicECNDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECNB.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicECNDB

end
