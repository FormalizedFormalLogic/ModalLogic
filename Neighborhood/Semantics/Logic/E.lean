module

public import Neighborhood.Semantics.Hilbert
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomGeach
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Hilbert.Logics
public import Neighborhood.Semantics.Example.Frame1_2

/-!
# The neighborhood logic `LogicE`

Soundness, consistency and completeness of `LogicE`, the weakest classical modal logic, with
respect to all neighborhood frames. Its strict inclusions in the stronger logics live in the
stronger logics' modules.

Also defines two auxiliary countermodels, `frame_1_0` and
`frame_2_8`, reused by several other neighborhood logics.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicE.sound {κ} [Nonempty κ] (F : Frame κ) :
    A ∈ LogicE → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨⟩)

theorem LogicE.consistent : (@LogicE α).IsConsistent := by
  by_contra! hC
  simpa using LogicE.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicE α)) :=
  MaximalConsistentSet.nonempty LogicE.consistent

variable [DecidableEq α]

theorem LogicE.complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F ⊧ A) :
    A ∈ @LogicE α :=
  (basicCanonicity LogicE).mem_of_valid
    (h (basicCanonicity LogicE).toModel.toFrame (basicCanonicity LogicE).toModel.Val)

end
