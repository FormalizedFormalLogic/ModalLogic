module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Filtration
import Neighborhood.Semantics.Example.Frame1_2
import Neighborhood.Semantics.Example.Frame2_8

/-!
# The neighborhood logic `LogicE4`

Soundness, consistency and completeness of `LogicE4`, the classical modal logic axiomatised by
the transitivity axiom `Four`, with respect to the transitive neighborhood frames
(`Frame.IsTransitive`), together with its finite frame property. Also proves the strict
inclusion of `LogicE` in `LogicE4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicE4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsTransitive] :
    A ∈ LogicE4 → F ⊧ A :=
  Hilbert.sound (fun _ hB => by obtain ⟨_, rfl⟩ := hB; exact valid_axiomFour_of_isTransitive)

theorem LogicE4.consistent : (@LogicE4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicE4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicE4 α)) :=
  MaximalConsistentSet.nonempty LogicE4.consistent

variable [DecidableEq α]

theorem LogicE4.complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsTransitive] → F ⊧ A) :
    A ∈ @LogicE4 α :=
  (basicCanonicity LogicE4).mem_of_valid
    (h (basicCanonicity LogicE4).toModel.toFrame
      (basicCanonicity LogicE4).toModel.Val)

theorem LogicE4.finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.IsTransitive] → F ⊧ A) :
    A ∈ @LogicE4 α :=
  LogicE4.complete <| by
    intro κ _ F hF V x
    haveI : F.IsTransitive := hF
    let M : Model κ α := ⟨F, V⟩
    haveI : Finite (FilterEqvQuotient M A.subformulas) := FilterEqvQuotient.finite (by simp)
    apply (transitiveFiltration M A.subformulas).filtration_satisfies _ (by grind) |>.mp
    haveI : (transitiveFiltration M A.subformulas).toModel.toFrame.IsFinite := ⟨‹_›⟩
    exact h (transitiveFiltration M A.subformulas).toModel.toFrame
      (transitiveFiltration M A.subformulas).toModel.Val ⟦x⟧


theorem LogicE_ssubset_LogicE4 : @LogicE ℕ ⊂ LogicE4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hFour : Axioms.Four (.atom 0) ∈ (@LogicE ℕ) := h (ProvableHilbert.axm ⟨_, rfl⟩)
    exact frame_2_8.not_valid_axiomFour
      (LogicE.sound frame_2_8 hFour)

end
