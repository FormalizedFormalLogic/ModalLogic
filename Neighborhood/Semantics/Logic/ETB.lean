module

public import Neighborhood.Semantics.Logic.ET
public import Neighborhood.Semantics.Logic.EB
public import Neighborhood.Semantics.Logic.ENT
public import Neighborhood.Semantics.Logic.ENB
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_9471106

/-!
# The neighborhood logic `LogicETB`

Soundness, consistency and completeness of `LogicETB`, the classical modal logic axiomatised by
both the reflexivity axiom `T` and the symmetry axiom `B`, with respect to the neighborhood
frames that are both reflexive and symmetric, and its strict inclusions in `LogicET`, `LogicEB`
and `LogicENT`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicETB.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsReflexive]
    [F.IsSymmetric] :
    A ∈ LogicETB → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

theorem LogicETB.consistent : (@LogicETB α).IsConsistent := by
  by_contra! hC
  simpa using LogicETB.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicETB α)) :=
  MaximalConsistentSet.nonempty LogicETB.consistent

section

variable [DecidableEq α]

/-- The intermediate canonical model of `intermediateRelativeMaximalCanonicity` is reflexive as
well as symmetric.

- [Che80, Exercise 9.39(b)] -/
theorem LogicETB.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsReflexive] → [F.IsSymmetric] → F ⊧ A) :
    A ∈ @LogicETB α :=
  (intermediateRelativeMaximalCanonicity LogicETB).mem_of_valid
    (h (intermediateRelativeMaximalCanonicity LogicETB).toModel.toFrame
      (intermediateRelativeMaximalCanonicity LogicETB).toModel.Val)

end

theorem LogicET_ssubset_LogicETB : @LogicET ℕ ⊂ LogicETB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hB : Axioms.B #0 ∈ @LogicET ℕ := h (ProvableHilbert.axm (by grind))
    have hS := isSymmetric_of_valid_axiomB (LogicET.sound frame_1_0 hB)
    have := hS.symm (X := Set.univ)
    simp [Frame.box, Frame.dia] at this

theorem LogicEB_ssubset_LogicETB : @LogicEB ℕ ⊂ LogicETB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hT : Axioms.T #0 ∈ @LogicEB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_isReflexive (isReflexive_of_valid_axiomT (LogicEB.sound frame_1_3 hT))

theorem LogicENT_ssubset_LogicENTB : @LogicENT ℕ ⊂ LogicENTB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hB : Axioms.B #0 ∈ @LogicENT ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_9471106.not_valid_axiomB (LogicENT.sound frame_3_9471106 hB)

theorem LogicENB_ssubset_LogicENTB : @LogicENB ℕ ⊂ LogicENTB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hT : Axioms.T #0 ∈ @LogicENB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_isReflexive
      (isReflexive_of_valid_axiomT (LogicENB.sound frame_1_3 hT))

theorem LogicENB_ssubset_LogicETB : @LogicENB ℕ ⊂ LogicETB := by
  rw [LogicETB_eq_LogicENTB]
  exact LogicENB_ssubset_LogicENTB

end
