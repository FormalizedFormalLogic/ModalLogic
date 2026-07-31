module

public import Neighborhood.Semantics.Logic.ET
public import Neighborhood.Semantics.Logic.EB
public import Neighborhood.Semantics.Logic.ENT
public import Neighborhood.Semantics.Logic.ENB
public import Neighborhood.Semantics.Logic.ENDB
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_9471106
public import Neighborhood.Logic.Equiv.ETB_ENTB

/-!
# The neighborhood logic `LogicETB`

Soundness, consistency and completeness of `LogicETB`, the classical modal logic axiomatised by
both the reflexivity axiom `T` and the symmetry axiom `B`, with respect to the neighborhood
frames that are both reflexive and symmetric.
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

theorem LogicENT_ssubset_LogicENTB : @LogicENT ℕ ⊂ LogicENTB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hB : Axioms.B #0 ∈ @LogicENT ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_9471106.not_valid_axiomB (LogicENT.sound frame_3_9471106 hB)

theorem LogicENDB_ssubset_LogicETB : @LogicENDB ℕ ⊂ LogicETB := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomB
  · intro h
    have hT : Axioms.T #0 ∈ @LogicENDB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomT (LogicENDB.sound frame_2_140 hT)

end
