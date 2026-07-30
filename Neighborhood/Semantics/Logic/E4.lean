module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Filtration

/-!
# The neighborhood logic `LogicE4`

Soundness, consistency and completeness of `LogicE4`, the classical modal logic axiomatised by
the transitivity axiom `Four`, with respect to the transitive neighborhood frames
(`Frame.IsTransitive`), together with its finite frame property. Also proves the strict
inclusion of `LogicE` in `LogicE4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

/-! ### Soundness, consistency and completeness -/

instance : Frame.simple_blackhole.IsTransitive where
  trans X := by
    intro x hx
    simp only [Frame.box, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
    subst hx
    simp [Frame.box]

/-- `LogicE4` is sound with respect to every transitive neighborhood frame. -/
theorem LogicE4.sound (h : A ∈ LogicE4) {κ} [Nonempty κ] (F : Frame κ) [F.IsTransitive] :
    F ⊧ A :=
  Hilbert.sound (fun _ hB => by obtain ⟨_, rfl⟩ := hB; exact valid_axiomFour_of_isTransitive) h

instance : (@LogicE4 α).Consistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole)
    (fun _ hB => by obtain ⟨_, rfl⟩ := hB; exact valid_axiomFour_of_isTransitive)

variable [DecidableEq α]

/-- `LogicE4` is complete with respect to all transitive neighborhood frames. -/
theorem LogicE4.complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.IsTransitive → F ⊧ A) :
    A ∈ @LogicE4 α :=
  (basicCanonicity LogicE4).mem_of_valid
    (h (basicCanonicity LogicE4).toModel.toFrame inferInstance
      (basicCanonicity LogicE4).toModel.Val)

/-- `LogicE4` is complete with respect to the finite transitive neighborhood frames (its finite
frame property). -/
theorem LogicE4.finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.IsFinite → F.IsTransitive → F ⊧ A) :
    A ∈ @LogicE4 α :=
  LogicE4.complete <| by
    intro κ _ F hF V x
    haveI : F.IsTransitive := hF
    let M : Model κ α := ⟨F, V⟩
    haveI : Finite (FilterEqvQuotient M A.subformulas) := FilterEqvQuotient.finite (by simp)
    apply (transitiveFiltration M A.subformulas).filtration_satisfies _ (by grind) |>.mp
    exact h (transitiveFiltration M A.subformulas).toModel.toFrame ⟨‹_›⟩
      transitiveFiltration.isTransitive (transitiveFiltration M A.subformulas).toModel.Val ⟦x⟧

/-! ### Strict inclusion of `LogicE` -/

theorem LogicE_ssubset_LogicE4 : @LogicE ℕ ⊂ LogicE4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hFour : Axioms.Four (.atom 0) ∈ (@LogicE ℕ) := h (ProvableHilbert.axm ⟨_, rfl⟩)
    exact Frame.trivial_nontransitive.not_valid_axiomFour
      (LogicE.sound hFour Frame.trivial_nontransitive)

end
