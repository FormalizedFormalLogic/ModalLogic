module

public import Neighborhood.Logic.Logic.EN
public import Neighborhood.Logic.Logic.EB
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_9472136

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsSymmetric] :
    A ∈ LogicENB → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp)

instance : (@LogicENB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENB.sound frame_1_2 hC⟩

/-- The intermediate canonical model of `intermediateRelativeMaximalCanonicalModel` contains its
unit as well as being symmetric.

- [Che80, Exercise 9.39(b)] -/
theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.IsSymmetric] → F ⊧ A) :
    A ∈ @LogicENB α :=
  (intermediateRelativeMaximalCanonicalModel LogicENB).mem_of_valid
    (h (intermediateRelativeMaximalCanonicalModel LogicENB).toFrame
      (intermediateRelativeMaximalCanonicalModel LogicENB).Val)

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENB α) := by
  by_contra! hcon
  exact frame_3_9488552.not_valid_axiomC hab (LogicENB.sound frame_3_9488552 (hcon #a #b))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicENB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicENB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour
    (Hilbert.sound (F := frame_2_140) (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp) (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicENB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicENB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicENB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicENB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicENB α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicENB.sound frame_1_3 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicENB.sound frame_2_140 (hcon #a))

end LogicENB

theorem LogicENB.ssubset_LogicEN : @LogicEN ℕ ⊂ LogicENB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEN.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicENB.ssubset_LogicEB : @LogicEB ℕ ⊂ LogicENB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEB.not_provable_axiomN⟩

end
