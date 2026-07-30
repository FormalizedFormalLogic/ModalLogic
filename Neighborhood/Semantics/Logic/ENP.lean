module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.AxiomN

/-!
# The neighborhood logic `LogicENP`

Soundness, consistency and completeness of `LogicENP`, the classical modal logic axiomatised by
both `N := □⊤` and the possibility axiom `P` over `LogicE`, with respect to the neighborhood
frames that contain their unit and in which no world has the empty set as one of its
neighborhoods.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicENP.sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.NotContainsEmpty] :
    A ∈ LogicENP → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | rfl) <;> simp)

theorem LogicENP.consistent : (@LogicENP α).IsConsistent := by
  by_contra! hC
  simpa using LogicENP.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicENP α)) :=
  MaximalConsistentSet.nonempty LogicENP.consistent

variable [DecidableEq α]

theorem LogicENP.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicENP α :=
  (basicCanonicity LogicENP).mem_of_valid
    (h (basicCanonicity LogicENP).toModel.toFrame
      (basicCanonicity LogicENP).toModel.Val)

end
