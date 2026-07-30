module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Example.Frame1_2

/-!
# The neighborhood logic `LogicENB`

Soundness, consistency and completeness of `LogicENB`, the classical modal logic axiomatised by
`N := □⊤` and the symmetry axiom `B` over `LogicE`, with respect to the neighborhood frames that
contain their unit and are symmetric.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicENB.sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsSymmetric] :
    A ∈ LogicENB → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp)

theorem LogicENB.consistent : (@LogicENB α).IsConsistent := by
  by_contra! hC
  simpa using LogicENB.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicENB α)) :=
  MaximalConsistentSet.nonempty LogicENB.consistent

section

variable [DecidableEq α]

/-- The intermediate canonical model of `intermediateRelativeMaximalCanonicity` contains its
unit as well as being symmetric.

- [Che80, Exercise 9.39(b)] -/
theorem LogicENB.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.IsSymmetric] → F ⊧ A) :
    A ∈ @LogicENB α :=
  (intermediateRelativeMaximalCanonicity LogicENB).mem_of_valid
    (h (intermediateRelativeMaximalCanonicity LogicENB).toModel.toFrame
      (intermediateRelativeMaximalCanonicity LogicENB).toModel.Val)

end

end
