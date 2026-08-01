module

public import Neighborhood.Logic.Logic.ENT
public import Neighborhood.Logic.Logic.ENDB
public import Neighborhood.Semantics.Example.Frame3_8437920
public import Neighborhood.Semantics.Example.Frame3_9472136

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicETB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsReflexive]
    [F.IsSymmetric] :
    A ∈ LogicETB → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicETB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicETB.sound frame_1_2 hC⟩

/-- The intermediate canonical model of `intermediateRelativeMaximalCanonicalModel` is reflexive as
well as symmetric.

- [Che80, Exercise 9.39(b)] -/
theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsReflexive] → [F.IsSymmetric] → F ⊧ A) :
    A ∈ @LogicETB α :=
  (intermediateRelativeMaximalCanonicalModel LogicETB).mem_of_valid
    (h (intermediateRelativeMaximalCanonicalModel LogicETB).toFrame
      (intermediateRelativeMaximalCanonicalModel LogicETB).Val)

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicETB α) := by
  by_contra! hcon
  exact frame_3_9488552.not_valid_axiomC hab (LogicETB.sound frame_3_9488552 (hcon #a #b))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicETB α) := by
  by_contra! hcon
  exact frame_3_8437920.not_valid_axiomFive (LogicETB.sound frame_3_8437920 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicETB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicETB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicETB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicETB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicETB α) := by
  by_contra! hcon
  exact frame_3_8437920.not_valid_axiomFour (LogicETB.sound frame_3_8437920 (hcon #a))

theorem ssubset_LogicENDB : @LogicENDB ℕ ⊂ LogicETB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicENDB.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicETB

end
