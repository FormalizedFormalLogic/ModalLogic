module

public import Neighborhood.Logic.Logic.ECND
public import Neighborhood.Logic.Logic.ECN4
public import Neighborhood.Logic.Logic.END4
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_8553090

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECND4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] [F.IsSerial] [F.IsTransitive] :
    A ∈ LogicECND4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECND4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECND4.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECND4 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicECND4.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECND4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicECND4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECND4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicECND4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECND4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicECND4.sound frame_2_138 (hcon #a))

theorem ssubset_LogicECND : @LogicECND ℕ ⊂ LogicECND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECND.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECN4 : @LogicECN4 ℕ ⊂ LogicECND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECN4.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEND4 : @LogicEND4 ℕ ⊂ LogicECND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEND4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicECND4

end
