module

public import Neighborhood.Logic.Logic.EMT4
public import Neighborhood.Logic.Logic.EMN
public import Neighborhood.Logic.Logic.EMN4
public import Neighborhood.Logic.Logic.EMNT
public import Neighborhood.Logic.Logic.ENT4
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_10520744

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMNT4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.ContainsUnit] [F.IsReflexive] [F.IsTransitive] :
    A ∈ LogicEMNT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMNT4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMNT4.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] →
      [F.IsReflexive] → [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMNT4 α :=
  (supplementedBasicCanonicalModel LogicEMNT4).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMNT4).toFrame
      (supplementedBasicCanonicalModel LogicEMNT4).Val)

theorem finite_complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.IsMonotonic] →
      [F.ContainsUnit] → [F.IsReflexive] → [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMNT4 α :=
  LogicEMNT4.complete <| by
    intro κ _ F hMono hUnit hRefl hTrans V x
    let M : Model κ α := ⟨F, V⟩
    let T : FormulaSet α := (A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas
    haveI : Finite (FilterEqvQuotient M T) := FilterEqvQuotient.finite (by simp [T])
    haveI := supplementedTransitiveFiltration.containsUnit (M := M) (T := T) (by simp [T])
    apply (supplementedTransitiveFiltration M T).filtration_satisfies _ (by simp [T]) |>.mp
    haveI : (supplementedTransitiveFiltration M T).toModel.toFrame.IsFinite := ⟨‹_›⟩
    exact h (supplementedTransitiveFiltration M T).toModel.toFrame
      (supplementedTransitiveFiltration M T).toModel.Val ⟦x⟧

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMNT4 α) := by
  by_contra! hcon
  exact frame_3_10520744.not_valid_axiomC hab (LogicEMNT4.sound frame_3_10520744 (hcon #a #b))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMNT4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEMNT4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMNT4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEMNT4.sound frame_2_138 (hcon #a))

theorem ssubset_LogicEMT4 : @LogicEMT4 ℕ ⊂ LogicEMNT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEMT4.not_provable_axiomN⟩

theorem ssubset_LogicENT4 : @LogicENT4 ℕ ⊂ LogicEMNT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicENT4.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMN4 : @LogicEMN4 ℕ ⊂ LogicEMNT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMN4.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicEMNT : @LogicEMNT ℕ ⊂ LogicEMNT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMNT.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, ProvableHilbert.axm (by grind), hA⟩

end LogicEMNT4

end
