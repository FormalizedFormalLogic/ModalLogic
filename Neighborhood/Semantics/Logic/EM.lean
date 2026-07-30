module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Supplementation
import Neighborhood.Semantics.Example.Frame1_2

/-!
# The neighborhood logic `LogicEM`

Soundness, consistency and completeness of `LogicEM`, the classical modal logic axiomatised by
the monotonicity axiom `M`, with respect to all monotonic neighborhood frames.

Also proves the strict inclusion of `LogicE` in `LogicEM` (a comparison of two logics lives in
the stronger logic's module).
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEM.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] :
    A ∈ LogicEM → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, _, rfl⟩; exact valid_axiomM_of_isMonotonic)

theorem LogicEM.consistent : (@LogicEM α).IsConsistent := by
  by_contra! hC
  simpa using LogicEM.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEM α)) :=
  MaximalConsistentSet.nonempty LogicEM.consistent

variable [DecidableEq α]

theorem LogicEM.complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → F ⊧ A) :
    A ∈ @LogicEM α :=
  (supplementedBasicCanonicity LogicEM).mem_of_valid
    (h (supplementedBasicCanonicity LogicEM).toModel.toFrame
      (supplementedBasicCanonicity LogicEM).toModel.Val)


theorem LogicE_ssubset_LogicEM : @LogicE ℕ ⊂ LogicEM := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hM : Axioms.M (.atom 0) (.atom 1) ∈ (@LogicE ℕ) := h (ProvableHilbert.axm ⟨_, _, rfl⟩)
    let M : Model (Fin 3) ℕ :=
      ⟨⟨fun w => match w with
        | 0 => {{1}}
        | 1 => {{0}, {0, 1}}
        | 2 => {{0}, {1, 2}}⟩,
       fun a => match a with
        | 0 => {0, 1}
        | 1 => {1, 2}
        | _ => Set.univ⟩
    have h0 := LogicE.sound M.toFrame hM M.Val 0
    simp [M, Forces, Frame.box, Set.ext_iff] at h0
    grind

end
