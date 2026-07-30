module

public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Filtration
import Mathlib.Tactic.FinCases
import Neighborhood.Semantics.Example.SimpleBlackhole
import Neighborhood.Semantics.Example.SimpleWhitehole
import Neighborhood.Semantics.Example.TrivialContainsUnit

/-!
# The neighborhood logic `LogicEN4`

Soundness, consistency and completeness of `LogicEN4`, the classical modal logic axiomatised by
both `N := □⊤` and the transitivity axiom `Four` over `LogicE`, with respect to the transitive
neighborhood frames containing their unit, together with its finite frame property. Also proves
the strict inclusions of `LogicEN` and `LogicE4` in `LogicEN4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEN4.sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsTransitive] :
    A ∈ LogicEN4 → F ⊧ A :=
  Hilbert.sound
    (fun _ hB => by
      rcases hB with rfl | ⟨_, rfl⟩
      · exact valid_axiomN_of_containsUnit
      · exact valid_axiomFour_of_isTransitive)

theorem LogicEN4.consistent : (@LogicEN4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEN4.sound Frame.simple_blackhole hC

instance : Nonempty (MaximalConsistentSet (@LogicEN4 α)) :=
  MaximalConsistentSet.nonempty LogicEN4.consistent

variable [DecidableEq α]

theorem LogicEN4.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.IsTransitive] → F ⊧ A) :
    A ∈ @LogicEN4 α :=
  (basicCanonicity LogicEN4).mem_of_valid
    (h (basicCanonicity LogicEN4).toModel.toFrame
      (basicCanonicity LogicEN4).toModel.Val)

instance : FormulaSet.IsSubformulaClosed
    ((A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas) where
  closed B hB C hC := by
    rcases hB with hB | hB
    · exact Or.inl (Formula.subformulas.subset_of_mem hB hC)
    · exact Or.inr (Formula.subformulas.subset_of_mem hB hC)

theorem LogicEN4.finite_complete
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

theorem LogicEN_ssubset_LogicEN4 : @LogicEN ℕ ⊂ LogicEN4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four (.atom 0) ∈ (@LogicEN ℕ) := h (ProvableHilbert.axm (Or.inr ⟨_, rfl⟩))
    exact Frame.trivial_containsUnit.not_valid_axiomFour
      (LogicEN.sound Frame.trivial_containsUnit hFour)

theorem LogicE4_ssubset_LogicEN4 : @LogicE4 ℕ ⊂ LogicEN4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ (@LogicE4 ℕ) := h (ProvableHilbert.axm (Or.inl rfl))
    exact Frame.simple_whitehole.not_valid_axiomN (LogicE4.sound Frame.simple_whitehole hN)

end
