module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_9488552
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_3346281

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSymmetric] :
    A ∈ LogicEB → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, rfl⟩; simp)

instance : (@LogicEB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEB.sound frame_1_2 hC⟩

/-- Neither the smallest nor the largest canonical model is symmetric, but the intermediate one
of `intermediateRelativeMaximalCanonicalModel` is.

- [Che80, Exercise 9.39(b)] -/
theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsSymmetric] → F ⊧ A) :
    A ∈ @LogicEB α :=
  (intermediateRelativeMaximalCanonicalModel LogicEB).mem_of_valid
    (h (intermediateRelativeMaximalCanonicalModel LogicEB).toFrame
      (intermediateRelativeMaximalCanonicalModel LogicEB).Val)

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEB α) := by
  by_contra! hcon
  exact frame_3_9488552.not_valid_axiomC hab (LogicEB.sound frame_3_9488552 (hcon #a #b))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD
    (LogicEB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomN (LogicEB.sound frame_1_1 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEB α) := by
  by_contra! hcon
  exact frame_3_3346281.not_valid_axiomK hab (LogicEB.sound frame_3_3346281 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEB α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomM hab (LogicEB.sound frame_1_1 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicEB.sound frame_1_1 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEB α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicEB.sound frame_1_1 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEB.sound frame_2_140 (hcon #a))

end LogicEB

theorem LogicE_ssubset_LogicEB : (@LogicE ℕ) ⊂ LogicEB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · obtain ⟨A, hA⟩ := LogicE.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

end
