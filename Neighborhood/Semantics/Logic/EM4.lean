module

public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Filtration
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame3_9471106

/-!
# The neighborhood logic `LogicEM4`

Soundness, consistency and completeness of `LogicEM4`, the classical modal logic axiomatised by
the monotonicity axiom `M` and the transitivity axiom `Four`, with respect to the neighborhood
frames that are monotonic and transitive, together with its finite frame property.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEM4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsTransitive] :
    A ∈ LogicEM4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

theorem LogicEM4.consistent : (@LogicEM4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEM4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEM4 α)) :=
  MaximalConsistentSet.nonempty LogicEM4.consistent

variable [DecidableEq α]

theorem LogicEM4.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsTransitive] → F ⊧ A) :
    A ∈ @LogicEM4 α :=
  (supplementedBasicCanonicity LogicEM4).mem_of_valid
    (h (supplementedBasicCanonicity LogicEM4).toModel.toFrame
      (supplementedBasicCanonicity LogicEM4).toModel.Val)

theorem LogicEM4.finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.IsMonotonic] →
      [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEM4 α :=
  LogicEM4.complete <| by
    intro κ _ F hMono hTrans V x
    let M : Model κ α := ⟨F, V⟩
    haveI : Finite (FilterEqvQuotient M A.subformulas) := FilterEqvQuotient.finite (by simp)
    apply (supplementedTransitiveFiltration M A.subformulas).filtration_satisfies _
      (by grind) |>.mp
    haveI : (supplementedTransitiveFiltration M A.subformulas).toModel.toFrame.IsFinite := ⟨‹_›⟩
    exact h (supplementedTransitiveFiltration M A.subformulas).toModel.toFrame
      (supplementedTransitiveFiltration M A.subformulas).toModel.Val ⟦x⟧


theorem LogicE4_ssubset_LogicEM4 : @LogicE4 ℕ ⊂ LogicEM4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicE4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_9471106.not_valid_axiomM (LogicE4.sound frame_3_9471106 hM)

theorem LogicEM_ssubset_LogicEM4 : @LogicEM ℕ ⊂ LogicEM4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicEM ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_8.not_valid_axiomFour (LogicEM.sound frame_2_8 hFour)

end
