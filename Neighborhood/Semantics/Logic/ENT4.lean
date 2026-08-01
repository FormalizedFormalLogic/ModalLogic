module

public import Neighborhood.Semantics.Logic.ET4
public import Neighborhood.Semantics.Logic.ENT
public import Neighborhood.Semantics.Logic.END4
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_9471106

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENT4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsReflexive] [F.IsTransitive]
  : A ∈ LogicENT4 → F ⊧ A := Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicENT4 α).IsConsistent := ⟨by
  by_contra! hC;
  simpa using LogicENT4.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
  (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.IsReflexive] → [F.IsTransitive] → F ⊧ A) :
  A ∈ @LogicENT4 α :=
  (basicCanonicalModel LogicENT4).mem_of_valid $ h (basicCanonicalModel LogicENT4).toFrame (basicCanonicalModel LogicENT4).Val

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENT4 α) := by
  by_contra! hcon
  exact frame_3_10520744.not_valid_axiomC hab (LogicENT4.sound frame_3_10520744 (hcon #a #b))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENT4 α) := by
  by_contra! hcon
  exact frame_3_9471106.not_isEuclidean
    (isEuclidean_of_valid_axiomFive (LogicENT4.sound frame_3_9471106 (hcon #a)))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENT4 α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicENT4.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENT4 α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomK hab (LogicENT4.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicENT4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicENT4.sound frame_2_138 (hcon #a))

end LogicENT4

instance [DecidableEq α] : FormulaSet.IsSubformulaClosed
    ((A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas) where
  closed B hB C hC := by
    rcases hB with hB | hB
    · exact Or.inl (Formula.subformulas.subset_of_mem hB hC)
    · exact Or.inr (Formula.subformulas.subset_of_mem hB hC)

theorem LogicENT4.finite_complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.ContainsUnit] → [F.IsReflexive] →
      [F.IsTransitive] → F ⊧ A) :
    A ∈ @LogicENT4 α :=
  LogicENT4.complete <| by
    intro κ _ F hUnit hRefl hTrans V x
    haveI : F.IsReflexive := hRefl
    haveI : F.IsTransitive := hTrans
    let M : Model κ α := ⟨F, V⟩
    let T : FormulaSet α := (A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas
    haveI : Finite (FilterEqvQuotient M T) := FilterEqvQuotient.finite (by simp [T])
    haveI := transitiveFiltration.containsUnit (M := M) (T := T) (by simp [T])
    apply (transitiveFiltration M T).filtration_satisfies _ (by simp [T]) |>.mp
    haveI : (transitiveFiltration M T).toModel.toFrame.IsFinite := ⟨‹_›⟩
    exact h (transitiveFiltration M T).toModel.toFrame (transitiveFiltration M T).toModel.Val ⟦x⟧

theorem LogicET4_ssubset_LogicENT4 : @LogicET4 ℕ ⊂ LogicENT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.union_subset_union_left _ Set.subset_union_right)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicET4.not_provable_axiomN⟩

theorem LogicENT_ssubset_LogicENT4 : @LogicENT ℕ ⊂ LogicENT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicENT.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEND4_ssubset_LogicENT4 : @LogicEND4 ℕ ⊂ LogicENT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomFour
  · obtain ⟨A, hA⟩ := LogicEND4.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end
