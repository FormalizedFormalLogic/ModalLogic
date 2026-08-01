module

public import Neighborhood.Logic.Logic.END
public import Neighborhood.Logic.Logic.EN4
public import Neighborhood.Logic.Logic.ED4
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_8421506

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEND4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsSerial] [F.IsTransitive] :
    A ∈ LogicEND4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEND4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEND4.sound frame_1_2 hC⟩

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEND4 α) := by
  by_contra! hcon
  exact frame_3_8431784.not_valid_axiomC hab (LogicEND4.sound frame_3_8431784 (hcon #a #b))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEND4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive
    (LogicEND4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEND4 α) := by
  by_contra! hcon
  exact frame_3_8421506.not_valid_axiomM hab (LogicEND4.sound frame_3_8421506 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEND4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEND4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEND4 α) := by
  by_contra! hcon
  exact frame_3_8421506.not_valid_axiomK hab (LogicEND4.sound frame_3_8421506 (hcon #a #b))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEND4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEND4.sound frame_2_138 (hcon #a))

theorem ssubset_LogicEND : @LogicEND ℕ ⊂ LogicEND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEND.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEN4 : @LogicEN4 ℕ ⊂ LogicEND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms
      (Set.union_subset_union_left _ Set.subset_union_left)
  · obtain ⟨A, hA⟩ := LogicEN4.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicED4 : @LogicED4 ℕ ⊂ LogicEND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicED4.not_provable_axiomN⟩

end LogicEND4

end
