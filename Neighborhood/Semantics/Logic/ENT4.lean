module

public import Neighborhood.Semantics.Logic.EN4
public import Neighborhood.Semantics.Logic.ET4
public import Neighborhood.Semantics.Logic.ENT
public import Neighborhood.Semantics.Logic.END4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_8421512

/-!
# The neighborhood logic `LogicENT4`

Soundness, consistency and completeness of `LogicENT4`, the classical modal logic axiomatised by
`N := □⊤`, the reflexivity axiom `T` and the transitivity axiom `Four` over `LogicE`, with respect
to the neighborhood frames that contain their unit, are reflexive and are transitive, together
with its finite frame property.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicENT4

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsReflexive] [F.IsTransitive]
  : A ∈ LogicENT4 → F ⊧ A := Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
theorem consistent : (@LogicENT4 α).IsConsistent := by
  by_contra! hC;
  simpa using LogicENT4.sound frame_1_2 hC;

instance : Nonempty (MaximalConsistentSet (@LogicENT4 α)) :=
  MaximalConsistentSet.nonempty consistent

theorem complete
  (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.IsReflexive] → [F.IsTransitive] → F ⊧ A) :
  A ∈ @LogicENT4 α :=
  (basicCanonicity LogicENT4).mem_of_valid $ h (basicCanonicity LogicENT4).toModel.toFrame (basicCanonicity LogicENT4).toModel.Val

end LogicENT4

instance : FormulaSet.IsSubformulaClosed
    ((A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas) where
  closed B hB C hC := by
    rcases hB with hB | hB
    · exact Or.inl (Formula.subformulas.subset_of_mem hB hC)
    · exact Or.inr (Formula.subformulas.subset_of_mem hB hC)

theorem LogicENT4.finite_complete
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
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.union_subset_union_left _ Set.subset_union_right)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ (@LogicET4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicET4.sound frame_1_0 hN)

theorem LogicENT_ssubset_LogicENT4 : @LogicENT ℕ ⊂ LogicENT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicENT ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_8421512.not_valid_axiomFour
      (LogicENT.sound frame_3_8421512 hFour)

theorem LogicEND4_ssubset_LogicENT4 : @LogicEND4 ℕ ⊂ LogicENT4 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomFour
  · intro h
    have hT : Axioms.T #0 ∈ @LogicEND4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomT (LogicEND4.sound frame_2_170 hT)

end
