module

public import Neighborhood.Semantics.Logic.EMT
public import Neighborhood.Semantics.Logic.EM4
public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Logic.ET4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_9471106

/-!
# The neighborhood logic `LogicEMT4`

Soundness, consistency and completeness of `LogicEMT4`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the reflexivity axiom `T` and the transitivity axiom `Four`, with
respect to the neighborhood frames that are monotonic, reflexive and transitive, together with its
finite frame property. Also proves the strict inclusions of `LogicEMT`, `LogicET4` and `LogicEM4`
in `LogicEMT4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMT4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsReflexive] [F.IsTransitive] :
    A ∈ LogicEMT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMT4.consistent : (@LogicEMT4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMT4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMT4 α)) :=
  MaximalConsistentSet.nonempty LogicEMT4.consistent

variable [DecidableEq α]

theorem LogicEMT4.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsReflexive] →
      [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMT4 α :=
  (supplementedBasicCanonicity LogicEMT4).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMT4).toModel.toFrame
      (supplementedBasicCanonicity LogicEMT4).toModel.Val)

theorem LogicEMT4.finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.IsMonotonic] → [F.IsReflexive] →
      [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMT4 α :=
  LogicEMT4.complete <| by
    intro κ _ F hMono hRefl hTrans V x
    let M : Model κ α := ⟨F, V⟩
    haveI : Finite (FilterEqvQuotient M A.subformulas) := FilterEqvQuotient.finite (by simp)
    apply (supplementedTransitiveFiltration M A.subformulas).filtration_satisfies _
      (by grind) |>.mp
    haveI : (supplementedTransitiveFiltration M A.subformulas).toModel.toFrame.IsFinite := ⟨‹_›⟩
    exact h (supplementedTransitiveFiltration M A.subformulas).toModel.toFrame
      (supplementedTransitiveFiltration M A.subformulas).toModel.Val ⟦x⟧


theorem LogicEMT_ssubset_LogicEMT4 : @LogicEMT ℕ ⊂ LogicEMT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicEMT ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_8.not_valid_axiomFour
      (LogicEMT.sound frame_2_8 hFour)

theorem LogicET4_ssubset_LogicEMT4 : @LogicET4 ℕ ⊂ LogicEMT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicET4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_9471106.not_valid_axiomM (LogicET4.sound frame_3_9471106 hM)

theorem LogicEM4_ssubset_LogicEMT4 : @LogicEM4 ℕ ⊂ LogicEMT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hT : Axioms.T #0 ∈ (@LogicEM4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomT (LogicEM4.sound frame_2_170 hT)

end
