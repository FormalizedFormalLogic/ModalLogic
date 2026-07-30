module

public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Logic.ET
import Neighborhood.Semantics.Example.Frame1_2
import Neighborhood.Semantics.Example.Frame1_3

/-!
# The neighborhood logic `LogicEMT`

Soundness, consistency and completeness of `LogicEMT`, the classical modal logic axiomatised by
the monotonicity axiom `M` and the reflexivity axiom `T`, with respect to the neighborhood frames
that are both monotonic and reflexive, and its strict inclusion of `LogicEM`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMT.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsReflexive] :
    A ∈ LogicEMT → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

theorem LogicEMT.consistent : (@LogicEMT α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMT.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMT α)) :=
  MaximalConsistentSet.nonempty LogicEMT.consistent

variable [DecidableEq α]

theorem LogicEMT.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsReflexive] → F ⊧ A) :
    A ∈ @LogicEMT α :=
  (supplementedBasicCanonicity LogicEMT).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMT).toModel.toFrame
      (supplementedBasicCanonicity LogicEMT).toModel.Val)


theorem LogicEM_ssubset_LogicEMT : @LogicEM ℕ ⊂ LogicEMT := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hT : Axioms.T #0 ∈ @LogicEM ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_isReflexive (isReflexive_of_valid_axiomT (LogicEM.sound frame_1_3 hT))

end
