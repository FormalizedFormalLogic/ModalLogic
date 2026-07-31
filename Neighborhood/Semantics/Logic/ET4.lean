module

public import Neighborhood.Semantics.Logic.ET
public import Neighborhood.Semantics.Logic.ED4

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

lemma not_provable_axiomC {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicET4 α) := by
  by_contra! hcon
  exact frame_3_10520744.not_valid_axiomC hab (LogicET4.sound frame_3_10520744 (hcon #a #b))

lemma not_provable_axiomM {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicET4 α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicET4.sound frame_3_9471106 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicET4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicET4.sound frame_1_0 hcon)

end LogicET4

theorem LogicET_ssubset_LogicET4 : @LogicET ℕ ⊂ LogicET4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicET.not_provable_axiomFour (a := (0 : ℕ))
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicED4_ssubset_LogicET4 : @LogicED4 ℕ ⊂ LogicET4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact Logic.axiomD
    · exact ProvableHilbert.axm (by grind)
  · obtain ⟨A, hA⟩ := LogicED4.not_provable_axiomT (a := (0 : ℕ))
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end
