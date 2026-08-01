module

public import Neighborhood.Semantics.Logic.EMT
public import Neighborhood.Semantics.Logic.ET4
public import Neighborhood.Semantics.Logic.EMD4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame3_10520744

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMT4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsReflexive] [F.IsTransitive] :
    A ∈ LogicEMT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMT4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMT4.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsReflexive] →
      [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMT4 α :=
  (supplementedBasicCanonicalModel LogicEMT4).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMT4).toFrame
      (supplementedBasicCanonicalModel LogicEMT4).Val)

theorem finite_complete [DecidableEq α]
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

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMT4 α) := by
  by_contra! hcon
  exact frame_3_10520744.not_valid_axiomC hab (LogicEMT4.sound frame_3_10520744 (hcon #a #b))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMT4 α) := by
  by_contra! hcon
  exact frame_3_10520744.not_valid_axiomK hab (LogicEMT4.sound frame_3_10520744 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMT4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMT4.sound frame_1_0 hcon)

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMT4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMT4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMT4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMT4.sound frame_1_0 (hcon #a))

end LogicEMT4

theorem LogicEMT_ssubset_LogicEMT4 : @LogicEMT ℕ ⊂ LogicEMT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEMT.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicET4_ssubset_LogicEMT4 : @LogicET4 ℕ ⊂ LogicEMT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicET4.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMD4_ssubset_LogicEMT4 : @LogicEMD4 ℕ ⊂ LogicEMT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩)
    · exact ProvableHilbert.axm (by grind)
    · exact Logic.axiomD
    · exact ProvableHilbert.axm (by grind)
  · obtain ⟨A, hA⟩ := LogicEMD4.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end
