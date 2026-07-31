module

public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Logic.ET
public import Neighborhood.Semantics.Logic.EMD
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_9471106

/-!
# The neighborhood logic `LogicEMT`

Soundness, consistency and completeness of `LogicEMT`, the classical modal logic axiomatised by
the monotonicity axiom `M` and the reflexivity axiom `T`, with respect to the neighborhood frames
that are both monotonic and reflexive.
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

theorem LogicET_ssubset_LogicEMT : @LogicET ℕ ⊂ LogicEMT := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hM : Axioms.M #0 #1 ∈ @LogicET ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_9471106.not_valid_axiomM (LogicET.sound frame_3_9471106 hM)

theorem LogicEMD_ssubset_LogicEMT : @LogicEMD ℕ ⊂ LogicEMT := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩)
    · exact ProvableHilbert.axm (by grind)
    · exact Logic.axiomD
  · intro h
    have hT : Axioms.T #0 ∈ @LogicEMD ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomT (LogicEMD.sound frame_2_170 hT)

end
