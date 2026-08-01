module

public import Neighborhood.Logic.Logic.ECND
public import Neighborhood.Logic.Logic.ECN5
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_8553090
public import Neighborhood.Semantics.Example.Frame3_10529440

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECND5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] [F.IsSerial] [F.IsEuclidean] :
    A ∈ LogicECND5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECND5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECND5.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECND5 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicECND5.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECND5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicECND5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECND5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicECND5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECND5 α) := by
  by_contra! hcon
  exact frame_3_10529440.not_valid_axiomFour (LogicECND5.sound frame_3_10529440 (hcon #a))

theorem ssubset_LogicECND : @LogicECND ℕ ⊂ LogicECND5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECND.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECN5 : @LogicECN5 ℕ ⊂ LogicECND5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECN5.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicECND5

end
