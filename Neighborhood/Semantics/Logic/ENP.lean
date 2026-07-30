module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.AxiomN

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
