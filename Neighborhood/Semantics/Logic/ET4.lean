module

public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Logic.ET
public import Neighborhood.Semantics.Logic.ED4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_72
public import Neighborhood.Semantics.Example.Frame2_170

/-!
# The neighborhood logic `LogicET4`

Soundness, consistency and completeness of `LogicET4`, the classical modal logic axiomatised by
the reflexivity axiom `T` together with the transitivity axiom `Four`, with respect to the
neighborhood frames that are both reflexive and transitive, together with its finite frame
property.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicET4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsReflexive]
    [F.IsTransitive] :
    A ∈ LogicET4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicET4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicET4.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsReflexive] → [F.IsTransitive] → F ⊧ A) :
    A ∈ @LogicET4 α :=
  (basicCanonicalModel LogicET4).mem_of_valid
    (h (basicCanonicalModel LogicET4).toFrame
      (basicCanonicalModel LogicET4).Val)

theorem finite_complete
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

end LogicET4

theorem LogicET_ssubset_LogicET4 : @LogicET ℕ ⊂ LogicET4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four #0 ∈ @LogicET ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_72.not_isTransitive (isTransitive_of_valid_axiomFour (LogicET.sound frame_2_72 hFour))

theorem LogicED4_ssubset_LogicET4 : @LogicED4 ℕ ⊂ LogicET4 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact Logic.axiomD
    · exact ProvableHilbert.axm (by grind)
  · intro h
    have hT : Axioms.T #0 ∈ @LogicED4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomT (LogicED4.sound frame_2_170 hT)

end
