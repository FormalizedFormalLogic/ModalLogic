module

public import Neighborhood.Semantics.Logic.EN4
public import Neighborhood.Semantics.Logic.ET4
public import Neighborhood.Semantics.Filtration

/-!
# The neighborhood logic `LogicENT4`

Soundness, consistency and completeness of `LogicENT4`, the classical modal logic axiomatised by
`N := □⊤`, the reflexivity axiom `T` and the transitivity axiom `Four` over `LogicE`, with respect
to the neighborhood frames that contain their unit, are reflexive and are transitive, together
with its finite frame property. Also proves the strict inclusions of `LogicEN4` and `LogicET4` in
`LogicENT4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicENT4.sound (h : A ∈ LogicENT4) {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsReflexive] [F.IsTransitive] : F ⊧ A :=
  Hilbert.sound
    (by
      rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩)
      · exact valid_axiomN_of_containsUnit
      · exact valid_axiomT_of_isReflexive
      · exact valid_axiomFour_of_isTransitive) h

instance : (@LogicENT4 α).Consistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole)
    (by
      rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩)
      · exact valid_axiomN_of_containsUnit
      · exact valid_axiomT_of_isReflexive
      · exact valid_axiomFour_of_isTransitive)

variable [DecidableEq α]

theorem LogicENT4.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.ContainsUnit → F.IsReflexive →
      F.IsTransitive → F ⊧ A) :
    A ∈ @LogicENT4 α :=
  (basicCanonicity LogicENT4).mem_of_valid
    (h (basicCanonicity LogicENT4).toModel.toFrame inferInstance inferInstance inferInstance
      (basicCanonicity LogicENT4).toModel.Val)

instance : FormulaSet.IsSubformulaClosed
    ((A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas) where
  closed B hB C hC := by
    rcases hB with hB | hB
    · exact Or.inl (Formula.subformulas.subset_of_mem hB hC)
    · exact Or.inr (Formula.subformulas.subset_of_mem hB hC)

theorem LogicENT4.finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.IsFinite → F.ContainsUnit → F.IsReflexive →
      F.IsTransitive → F ⊧ A) :
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
    exact h (transitiveFiltration M T).toModel.toFrame ⟨‹_›⟩ ‹_› transitiveFiltration.isReflexive
      transitiveFiltration.isTransitive (transitiveFiltration M T).toModel.Val ⟦x⟧


abbrev Frame.trivial_containsUnit_transitive : Frame (Fin 2) := ⟨fun _ => {{(1 : Fin 2)}, Set.univ}⟩

instance : Frame.trivial_containsUnit_transitive.ContainsUnit := ⟨by
  ext x; simp [Frame.box, Frame.trivial_containsUnit_transitive]⟩

instance : Frame.trivial_containsUnit_transitive.IsTransitive where
  trans X := by
    intro x hx
    simp only [Frame.box, Frame.trivial_containsUnit_transitive, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hbox : Frame.trivial_containsUnit_transitive.box X = Set.univ := by
      ext y
      simp only [Frame.box, Frame.trivial_containsUnit_transitive, Set.mem_setOf_eq,
        Set.mem_univ, iff_true]
      rcases hx with rfl | rfl <;> simp
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, hbox]
    simp [Frame.box, Frame.trivial_containsUnit_transitive]

lemma Frame.trivial_containsUnit_transitive.not_isReflexive :
    ¬Frame.trivial_containsUnit_transitive.IsReflexive := by
  intro hR
  have h1 : (0 : Fin 2) ∈ Frame.trivial_containsUnit_transitive.box ({1} : Set (Fin 2)) := by
    simp [Frame.box, Frame.trivial_containsUnit_transitive]
  exact absurd (Frame.trivial_containsUnit_transitive.refl h1) (by simp)

lemma Frame.trivial_containsUnit_transitive.not_valid_axiomT :
    ¬Frame.trivial_containsUnit_transitive ⊧ (Axioms.T (.atom 0) : Formula ℕ) :=
  fun h => Frame.trivial_containsUnit_transitive.not_isReflexive (isReflexive_of_valid_axiomT h)

instance : Frame.simple_whitehole.IsReflexive :=
  ⟨fun X => by simp [Frame.box, Frame.simple_whitehole]⟩

theorem LogicEN4_ssubset_LogicENT4 : @LogicEN4 ℕ ⊂ LogicENT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.union_subset_union_left _ Set.subset_union_left)
  · intro h
    have hT : Axioms.T (.atom 0) ∈ (@LogicEN4 ℕ) :=
      h (ProvableHilbert.axm (Or.inl (Or.inr ⟨_, rfl⟩)))
    exact Frame.trivial_containsUnit_transitive.not_valid_axiomT
      (LogicEN4.sound hT Frame.trivial_containsUnit_transitive)

theorem LogicET4_ssubset_LogicENT4 : @LogicET4 ℕ ⊂ LogicENT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.union_subset_union_left _ Set.subset_union_right)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ (@LogicET4 ℕ) :=
      h (ProvableHilbert.axm (Or.inl (Or.inl rfl)))
    exact Frame.simple_whitehole.not_valid_axiomN (LogicET4.sound hN Frame.simple_whitehole)

end
