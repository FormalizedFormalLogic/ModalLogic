module

public import Neighborhood.Logic.Logic.EM4
public import Neighborhood.Logic.Logic.EMN
public import Neighborhood.Logic.Logic.EN4
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_206

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMN4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.ContainsUnit] [F.IsTransitive] :
    A ∈ LogicEMN4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMN4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMN4.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] →
      [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMN4 α :=
  (supplementedBasicCanonicalModel LogicEMN4).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMN4).toFrame
      (supplementedBasicCanonicalModel LogicEMN4).Val)

theorem finite_complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.IsMonotonic] →
      [F.ContainsUnit] → [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMN4 α :=
  LogicEMN4.complete <| by
    intro κ _ F hMono hUnit hTrans V x
    let M : Model κ α := ⟨F, V⟩
    let T : FormulaSet α := (A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas
    haveI : Finite (FilterEqvQuotient M T) := FilterEqvQuotient.finite (by simp [T])
    haveI := supplementedTransitiveFiltration.containsUnit (M := M) (T := T) (by simp [T])
    apply (supplementedTransitiveFiltration M T).filtration_satisfies _ (by simp [T]) |>.mp
    haveI : (supplementedTransitiveFiltration M T).toModel.toFrame.IsFinite := ⟨‹_›⟩
    exact h (supplementedTransitiveFiltration M T).toModel.toFrame
      (supplementedTransitiveFiltration M T).toModel.Val ⟦x⟧

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMN4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive
    (Hilbert.sound (F := frame_2_138) (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)
      (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMN4 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicEMN4.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMN4 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicEMN4.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMN4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMN4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMN4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEMN4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMN4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMN4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMN4 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMN4.sound frame_1_3 hcon)

theorem ssubset_LogicEM4 : @LogicEM4 ℕ ⊂ LogicEMN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEM4.not_provable_axiomN⟩

theorem ssubset_LogicEMN : @LogicEMN ℕ ⊂ LogicEMN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMN.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEN4 : @LogicEN4 ℕ ⊂ LogicEMN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEN4.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMN4

end
