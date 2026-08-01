module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_75
public import Neighborhood.Semantics.Example.Frame3_10528928
public import Neighborhood.Semantics.Example.Frame2_153
public import Neighborhood.Semantics.Example.Frame2_170

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicE5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsEuclidean] :
    A ∈ @LogicE5 α → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, rfl⟩; simp)

instance : (@LogicE5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicE5.sound frame_1_2 hC⟩

theorem complete [DecidableEq α] (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsEuclidean] → F ⊧ A) :
    A ∈ @LogicE5 α :=
  (maximalRelativeMaximalCanonicalModel LogicE5).mem_of_valid
    (h (maximalRelativeMaximalCanonicalModel LogicE5).toFrame
      (maximalRelativeMaximalCanonicalModel LogicE5).Val)

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicE5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomC hab (LogicE5.sound frame_3_10528928 (hcon #a #b))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicE5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD
    (LogicE5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicE5 α) := by
  by_contra! hcon
  exact frame_2_79.not_valid_axiomFour
    (LogicE5.sound frame_2_79 (hcon #a))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicE5 α) := by
  intro hcon
  exact frame_2_75.not_valid_axiomN (LogicE5.sound frame_2_75 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicE5 α) := by
  by_contra! hcon
  exact frame_1_3.not_isReflexive
    (isReflexive_of_valid_axiomT (LogicE5.sound frame_1_3 (hcon #a)))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicE5 α) := by
  by_contra! hcon
  exact frame_2_75.not_valid_axiomK hab (LogicE5.sound frame_2_75 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicE5 α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomM hab (LogicE5.sound frame_2_153 (hcon #a #b))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicE5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicE5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicE5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicE5.sound frame_1_3 hcon)

end LogicE5

theorem LogicE_ssubset_LogicE5 : @LogicE ℕ ⊂ LogicE5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · obtain ⟨A, hA⟩ := LogicE.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

end
