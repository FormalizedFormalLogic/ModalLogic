module

public import Neighborhood.Logic.Logic.E
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_137520
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame2_75

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEC

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] :
    A ∈ LogicEC → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, _, rfl⟩; simp)

instance : (@LogicEC α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEC.sound frame_1_2 hC⟩

theorem complete [DecidableEq α] (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsRegular] → F ⊧ A) :
    A ∈ @LogicEC α :=
  (basicCanonicalModel LogicEC).mem_of_valid
    (h (basicCanonicalModel LogicEC).toFrame
      (basicCanonicalModel LogicEC).Val)

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEC α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEC.sound frame_1_0 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEC α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEC.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEC α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEC.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEC α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicEC.sound frame_1_1 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEC α) := by
  by_contra! hcon
  exact frame_3_137520.not_valid_axiomM hab (LogicEC.sound frame_3_137520 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEC α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEC.sound frame_1_0 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEC α) := by
  by_contra! hcon
  exact frame_2_75.not_valid_axiomK hab (LogicEC.sound frame_2_75 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEC α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEC.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEC α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicEC.sound frame_1_1 hcon)

theorem ssubset_LogicE : (@LogicE ℕ) ⊂ LogicEC := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · obtain ⟨A, B, hA⟩ := LogicE.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEC

end
