module

public import Neighborhood.Semantics.Logic.ENT
public import Neighborhood.Semantics.Logic.ENDB
public import Neighborhood.Logic.Equiv.ETB_ENTB
public import Neighborhood.Semantics.Example.Frame3_8437920

/-!
# The neighborhood logic `LogicETB`

Soundness, consistency and completeness of `LogicETB`, the classical modal logic axiomatised by
both the reflexivity axiom `T` and the symmetry axiom `B`, with respect to the neighborhood
frames that are both reflexive and symmetric.
-/

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

section

variable [DecidableEq α]

/-- The intermediate canonical model of `intermediateRelativeMaximalCanonicalModel` is reflexive as
well as symmetric.

- [Che80, Exercise 9.39(b)] -/
theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsReflexive] → [F.IsSymmetric] → F ⊧ A) :
    A ∈ @LogicETB α :=
  (intermediateRelativeMaximalCanonicalModel LogicETB).mem_of_valid
    (h (intermediateRelativeMaximalCanonicalModel LogicETB).toFrame
      (intermediateRelativeMaximalCanonicalModel LogicETB).Val)

end

lemma not_provable_axiomC [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicETB α) := by
  by_contra! hcon
  exact frame_3_9488552.not_valid_axiomC hab (LogicETB.sound frame_3_9488552 (hcon #a #b))

lemma not_provable_axiomFive {a : α} : ∃ A, Axioms.Five A ∉ (@LogicETB α) := by
  by_contra! hcon
  exact frame_3_8437920.not_valid_axiomFive (LogicETB.sound frame_3_8437920 (hcon #a))

end LogicETB

theorem LogicENT_ssubset_LogicENTB : @LogicENT ℕ ⊂ LogicENTB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicENT.not_provable_axiomB (a := (0 : ℕ))
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicENDB_ssubset_LogicETB : @LogicENDB ℕ ⊂ LogicETB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomB
  · obtain ⟨A, hA⟩ := LogicENDB.not_provable_axiomT (a := (0 : ℕ))
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end
