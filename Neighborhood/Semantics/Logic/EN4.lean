module

public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Example.Frame2_138

/-!
# The neighborhood logic `LogicEN4`

Soundness, consistency and completeness of `LogicEN4`, the classical modal logic axiomatised by
both `N := □⊤` and the transitivity axiom `Four` over `LogicE`, with respect to the transitive
neighborhood frames containing their unit, together with its finite frame property.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEN4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsTransitive] :
    A ∈ LogicEN4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEN4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEN4.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.IsTransitive] → F ⊧ A) :
    A ∈ @LogicEN4 α :=
  (basicCanonicalModel LogicEN4).mem_of_valid
    (h (basicCanonicalModel LogicEN4).toFrame
      (basicCanonicalModel LogicEN4).Val)

instance : FormulaSet.IsSubformulaClosed
    ((A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas) where
  closed B hB C hC := by
    rcases hB with hB | hB
    · exact Or.inl (Formula.subformulas.subset_of_mem hB hC)
    · exact Or.inr (Formula.subformulas.subset_of_mem hB hC)

theorem finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.ContainsUnit] → [F.IsTransitive] →
      F ⊧ A) : A ∈ @LogicEN4 α :=
  LogicEN4.complete <| by
    intro κ _ F hUnit hTrans V x
    let M : Model κ α := ⟨F, V⟩
    let T : FormulaSet α := (A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas
    haveI : Finite (FilterEqvQuotient M T) := FilterEqvQuotient.finite (by simp [T])
    haveI := transitiveFiltration.containsUnit (M := M) (T := T) (by simp [T])
    apply (transitiveFiltration M T).filtration_satisfies _ (by simp [T]) |>.mp
    haveI : (transitiveFiltration M T).toModel.toFrame.IsFinite := ⟨‹_›⟩
    exact h (transitiveFiltration M T).toModel.toFrame (transitiveFiltration M T).toModel.Val ⟦x⟧

omit [DecidableEq α] in
lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEN4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEN4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomC (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEN4 α) := by
  by_contra! hcon
  exact frame_3_10520744.not_valid_axiomC hab (LogicEN4.sound frame_3_10520744 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEN4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEN4.sound frame_1_3 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEN4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive
    (LogicEN4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomM (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEN4 α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicEN4.sound frame_3_9471106 (hcon #a #b))

end LogicEN4

theorem LogicEN_ssubset_LogicEN4 : @LogicEN ℕ ⊂ LogicEN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEN.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicE4_ssubset_LogicEN4 : @LogicE4 ℕ ⊂ LogicEN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicE4.not_provable_axiomN⟩

end
