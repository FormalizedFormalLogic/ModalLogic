module

public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Logic.ET
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_170

/-!
# The neighborhood logic `LogicENT`

Soundness, consistency and completeness of `LogicENT`, the classical modal logic axiomatised by
`N := □⊤` and the reflexivity axiom `T` over `LogicE`, with respect to the neighborhood frames
that contain their unit and are reflexive. Also proves the strict inclusions of `LogicEN` and
`LogicET` in `LogicENT`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicENT.sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsReflexive] :
    A ∈ LogicENT → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp)

theorem LogicENT.consistent : (@LogicENT α).IsConsistent := by
  by_contra! hC
  simpa using LogicENT.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicENT α)) :=
  MaximalConsistentSet.nonempty LogicENT.consistent

variable [DecidableEq α]

theorem LogicENT.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.IsReflexive] → F ⊧ A) :
    A ∈ @LogicENT α :=
  (basicCanonicity LogicENT).mem_of_valid
    (h (basicCanonicity LogicENT).toModel.toFrame
      (basicCanonicity LogicENT).toModel.Val)


theorem LogicEN_ssubset_LogicENT : @LogicEN ℕ ⊂ LogicENT := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hT : Axioms.T #0 ∈ @LogicEN ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomT (LogicEN.sound frame_2_170 hT)

theorem LogicET_ssubset_LogicENT : @LogicET ℕ ⊂ LogicENT := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicET ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicET.sound frame_1_0 hN)

end
