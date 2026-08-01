module

public import Neighborhood.Logic.Logic.END
public import Neighborhood.Logic.Logic.ED5
public import Neighborhood.Logic.Logic.EN5
public import Neighborhood.Semantics.Example.Frame3_8553090
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_10528928

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEND5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsSerial]
    [F.IsEuclidean] :
    A ∈ LogicEND5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEND5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEND5.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEND5 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicEND5.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEND5 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomK hab (LogicEND5.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEND5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomC hab (LogicEND5.sound frame_3_10528928 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEND5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEND5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEND5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEND5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEND5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomFour (LogicEND5.sound frame_3_10528928 (hcon #a))

theorem ssubset_LogicEND : @LogicEND ℕ ⊂ LogicEND5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEND.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicED5 : @LogicED5 ℕ ⊂ LogicEND5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicED5.not_provable_axiomN⟩

theorem ssubset_LogicEN5 : @LogicEN5 ℕ ⊂ LogicEND5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEN5.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEND5

end
