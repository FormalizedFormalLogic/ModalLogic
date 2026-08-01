module

public import Neighborhood.Logic.Logic.E4
public import Neighborhood.Logic.Logic.EM
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_206

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEM4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsTransitive] :
    A ∈ LogicEM4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEM4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEM4.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsTransitive] → F ⊧ A) :
    A ∈ @LogicEM4 α :=
  (supplementedBasicCanonicalModel LogicEM4).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEM4).toFrame
      (supplementedBasicCanonicalModel LogicEM4).Val)

theorem finite_complete [DecidableEq α]
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

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEM4 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab
    (LogicEM4.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEM4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEM4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEM4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEM4.sound frame_1_0 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEM4 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicEM4.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEM4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEM4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEM4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEM4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEM4 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEM4.sound frame_1_3 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEM4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEM4.sound frame_1_0 (hcon #a))

theorem ssubset_LogicE4 : @LogicE4 ℕ ⊂ LogicEM4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicE4.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEM : @LogicEM ℕ ⊂ LogicEM4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEM.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEM4

end
