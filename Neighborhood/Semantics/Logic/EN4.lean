module

public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Filtration
import Mathlib.Tactic.FinCases

/-!
# The neighborhood logic `LogicEN4`

Soundness, consistency and completeness of `LogicEN4`, the classical modal logic axiomatised by
both `N := □⊤` and the transitivity axiom `Four` over `LogicE`, with respect to the transitive
neighborhood frames containing their unit, together with its finite frame property. Also proves
the strict inclusions of `LogicEN` and `LogicE4` in `LogicEN4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEN4.sound (h : A ∈ LogicEN4) {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsTransitive] : F ⊧ A :=
  Hilbert.sound
    (fun _ hB => by
      rcases hB with rfl | ⟨_, rfl⟩
      · exact valid_axiomN_of_containsUnit
      · exact valid_axiomFour_of_isTransitive) h

instance : (@LogicEN4 α).Consistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole)
    (fun _ hB => by
      rcases hB with rfl | ⟨_, rfl⟩
      · exact valid_axiomN_of_containsUnit
      · exact valid_axiomFour_of_isTransitive)

variable [DecidableEq α]

theorem LogicEN4.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.ContainsUnit → F.IsTransitive → F ⊧ A) :
    A ∈ @LogicEN4 α :=
  (basicCanonicity LogicEN4).mem_of_valid
    (h (basicCanonicity LogicEN4).toModel.toFrame inferInstance inferInstance
      (basicCanonicity LogicEN4).toModel.Val)

instance : FormulaSet.IsSubformulaClosed
    ((A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas) where
  closed B hB C hC := by
    rcases hB with hB | hB
    · exact Or.inl (Formula.subformulas.subset_of_mem hB hC)
    · exact Or.inr (Formula.subformulas.subset_of_mem hB hC)

theorem LogicEN4.finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.IsFinite → F.ContainsUnit → F.IsTransitive →
      F ⊧ A) : A ∈ @LogicEN4 α :=
  LogicEN4.complete <| by
    intro κ _ F hUnit hTrans V x
    let M : Model κ α := ⟨F, V⟩
    let T : FormulaSet α := (A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas
    haveI : Finite (FilterEqvQuotient M T) := FilterEqvQuotient.finite (by simp [T])
    haveI := transitiveFiltration.containsUnit (M := M) (T := T) (by simp [T])
    apply (transitiveFiltration M T).filtration_satisfies _ (by simp [T]) |>.mp
    exact h (transitiveFiltration M T).toModel.toFrame ⟨‹_›⟩ ‹_›
      transitiveFiltration.isTransitive (transitiveFiltration M T).toModel.Val ⟦x⟧


abbrev Frame.trivial_containsUnit : Frame (Fin 2) := ⟨fun x => {{x}ᶜ, Set.univ}⟩

instance : Frame.trivial_containsUnit.ContainsUnit := ⟨by
  ext x; fin_cases x <;> simp [Frame.box, Frame.trivial_containsUnit]⟩

lemma Frame.trivial_containsUnit.not_isTransitive :
    ¬Frame.trivial_containsUnit.IsTransitive := by
  intro hC
  have hbox0 : Frame.trivial_containsUnit.box ({0} : Set (Fin 2)) = {1} := by
    ext y; fin_cases y <;> simp [Frame.box, Frame.trivial_containsUnit, Set.ext_iff]
  have hbox1 : Frame.trivial_containsUnit.box ({1} : Set (Fin 2)) = {0} := by
    ext y; fin_cases y <;> simp [Frame.box, Frame.trivial_containsUnit, Set.ext_iff]
  have hiter : Frame.trivial_containsUnit.box^[2] ({0} : Set (Fin 2)) = {0} := by
    show Frame.trivial_containsUnit.box (Frame.trivial_containsUnit.box {0}) = {0}
    rw [hbox0, hbox1]
  have h1 : (1 : Fin 2) ∈ Frame.trivial_containsUnit.box ({0} : Set (Fin 2)) := by
    rw [hbox0]; rfl
  have h2 := hC.trans ({0} : Set (Fin 2)) h1
  rw [hiter] at h2
  simp at h2

lemma Frame.trivial_containsUnit.not_valid_axiomFour :
    ¬Frame.trivial_containsUnit ⊧ (Axioms.Four (.atom 0) : Formula ℕ) :=
  fun h => Frame.trivial_containsUnit.not_isTransitive (isTransitive_of_valid_axiomFour h)

theorem LogicEN_ssubset_LogicEN4 : @LogicEN ℕ ⊂ LogicEN4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four (.atom 0) ∈ (@LogicEN ℕ) := h (ProvableHilbert.axm (Or.inr ⟨_, rfl⟩))
    exact Frame.trivial_containsUnit.not_valid_axiomFour
      (LogicEN.sound hFour Frame.trivial_containsUnit)

instance : Frame.simple_whitehole.IsTransitive where
  trans X := by simp [Frame.box]

theorem LogicE4_ssubset_LogicEN4 : @LogicE4 ℕ ⊂ LogicEN4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ (@LogicE4 ℕ) := h (ProvableHilbert.axm (Or.inl rfl))
    exact Frame.simple_whitehole.not_valid_axiomN (LogicE4.sound hN Frame.simple_whitehole)

end
