module

public import Neighborhood.Logic.Logic.ET
public import Neighborhood.Logic.Logic.ED4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame3_9471106

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

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsReflexive] → [F.IsTransitive] → F ⊧ A) :
    A ∈ @LogicET4 α :=
  (basicCanonicalModel LogicET4).mem_of_valid
    (h (basicCanonicalModel LogicET4).toFrame
      (basicCanonicalModel LogicET4).Val)

theorem finite_complete [DecidableEq α]
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

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicET4 α) := by
  by_contra! hcon
  exact frame_3_10520744.not_valid_axiomC hab (LogicET4.sound frame_3_10520744 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicET4 α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicET4.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicET4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicET4.sound frame_1_0 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicET4 α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomK hab (LogicET4.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicET4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicET4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicET4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicET4.sound frame_1_0 (hcon #a))

theorem ssubset_LogicET : @LogicET ℕ ⊂ LogicET4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicET.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicED4 : @LogicED4 ℕ ⊂ LogicET4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicED4.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicET4

end
