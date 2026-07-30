module

public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Logic.ET
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_72

/-!
# The neighborhood logic `LogicET4`

Soundness, consistency and completeness of `LogicET4`, the classical modal logic axiomatised by
the reflexivity axiom `T` together with the transitivity axiom `Four`, with respect to the
neighborhood frames that are both reflexive and transitive, together with its finite frame
property. Also proves the strict inclusions of `LogicE4` and `LogicET` in `LogicET4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicET4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsReflexive]
    [F.IsTransitive] :
    A ∈ LogicET4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

theorem LogicET4.consistent : (@LogicET4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicET4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicET4 α)) :=
  MaximalConsistentSet.nonempty LogicET4.consistent

variable [DecidableEq α]

theorem LogicET4.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsReflexive] → [F.IsTransitive] → F ⊧ A) :
    A ∈ @LogicET4 α :=
  (basicCanonicity LogicET4).mem_of_valid
    (h (basicCanonicity LogicET4).toModel.toFrame
      (basicCanonicity LogicET4).toModel.Val)

theorem LogicET4.finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.IsReflexive] → [F.IsTransitive] →
      F ⊧ A) :
    A ∈ @LogicET4 α :=
  LogicET4.complete <| by
    intro κ _ F hR hT V x
    haveI : F.IsReflexive := hR
    haveI : F.IsTransitive := hT
    let M : Model κ α := ⟨F, V⟩
    haveI : Finite (FilterEqvQuotient M A.subformulas) := FilterEqvQuotient.finite (by simp)
    apply (transitiveFiltration M A.subformulas).filtration_satisfies _ (by grind) |>.mp
    haveI : (transitiveFiltration M A.subformulas).toModel.toFrame.IsFinite := ⟨‹_›⟩
    exact h (transitiveFiltration M A.subformulas).toModel.toFrame
      (transitiveFiltration M A.subformulas).toModel.Val ⟦x⟧


theorem LogicE4_ssubset_LogicET4 : @LogicE4 ℕ ⊂ LogicET4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hT : Axioms.T #0 ∈ @LogicE4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_isReflexive (isReflexive_of_valid_axiomT (LogicE4.sound frame_1_3 hT))

theorem LogicET_ssubset_LogicET4 : @LogicET ℕ ⊂ LogicET4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four #0 ∈ @LogicET ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_72.not_isTransitive (isTransitive_of_valid_axiomFour (LogicET.sound frame_2_72 hFour))

end
