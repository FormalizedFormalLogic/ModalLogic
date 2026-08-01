module

public import Neighborhood.Logic.Logic.EC4
public import Neighborhood.Logic.Logic.EC5
public import Neighborhood.Logic.Logic.E45
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_75
public import Neighborhood.Semantics.Example.Frame2_153
public import Neighborhood.Semantics.Example.Frame2_170

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEC45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicEC45 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEC45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEC45.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEC45 α) := by
  by_contra! hcon
  exact frame_2_75.not_valid_axiomK hab (LogicEC45.sound frame_2_75 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEC45 α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomM hab (LogicEC45.sound frame_2_153 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEC45 α) := by
  intro hcon
  exact frame_2_75.not_valid_axiomN (LogicEC45.sound frame_2_75 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEC45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEC45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEC45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEC45.sound frame_2_170 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEC45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEC45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEC45 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEC45.sound frame_1_3 hcon)

end LogicEC45


theorem LogicEC45.ssubset_LogicEC4 : @LogicEC4 ℕ ⊂ LogicEC45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEC4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEC45.ssubset_LogicEC5 : @LogicEC5 ℕ ⊂ LogicEC45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEC5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEC45.ssubset_LogicE45 : @LogicE45 ℕ ⊂ LogicEC45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicE45.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
