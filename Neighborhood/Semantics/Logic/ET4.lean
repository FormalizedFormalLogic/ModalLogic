module

public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Logic.ET
public import Neighborhood.Semantics.Filtration

/-!
# The neighborhood logic `LogicET4`

Soundness, consistency and completeness of `LogicET4`, the classical modal logic axiomatised by
the reflexivity axiom `T` together with the transitivity axiom `Four`, with respect to the
neighborhood frames that are both reflexive and transitive, together with its finite frame
property. Also proves the strict inclusions of `LogicE4` and `LogicET` in `LogicET4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicET4.sound (h : A ∈ LogicET4) {κ} [Nonempty κ] (F : Frame κ) [F.IsReflexive]
    [F.IsTransitive] : F ⊧ A :=
  Hilbert.sound (by
    rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact valid_axiomT_of_isReflexive
    · exact valid_axiomFour_of_isTransitive) h

instance : (@LogicET4 α).Consistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole) (by
    rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact valid_axiomT_of_isReflexive
    · exact valid_axiomFour_of_isTransitive)

variable [DecidableEq α]

theorem LogicET4.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.IsReflexive → F.IsTransitive → F ⊧ A) :
    A ∈ @LogicET4 α :=
  (basicCanonicity LogicET4).mem_of_valid
    (h (basicCanonicity LogicET4).toModel.toFrame inferInstance inferInstance
      (basicCanonicity LogicET4).toModel.Val)

theorem LogicET4.finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.IsFinite → F.IsReflexive → F.IsTransitive →
      F ⊧ A) :
    A ∈ @LogicET4 α :=
  LogicET4.complete <| by
    intro κ _ F hR hT V x
    haveI : F.IsReflexive := hR
    haveI : F.IsTransitive := hT
    let M : Model κ α := ⟨F, V⟩
    haveI : Finite (FilterEqvQuotient M A.subformulas) := FilterEqvQuotient.finite (by simp)
    apply (transitiveFiltration M A.subformulas).filtration_satisfies _ (by grind) |>.mp
    exact h (transitiveFiltration M A.subformulas).toModel.toFrame ⟨‹_›⟩
      transitiveFiltration.isReflexive transitiveFiltration.isTransitive
      (transitiveFiltration M A.subformulas).toModel.Val ⟦x⟧


theorem LogicE4_ssubset_LogicET4 : @LogicE4 ℕ ⊂ LogicET4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hT : Axioms.T (.atom 0) ∈ @LogicE4 ℕ := h (ProvableHilbert.axm (Or.inl ⟨_, rfl⟩))
    haveI : (⟨fun _ => Set.univ⟩ : Frame (Fin 1)).IsTransitive := ⟨fun X => by simp [Frame.box]⟩
    have hR := isReflexive_of_valid_axiomT
      (LogicE4.sound hT (⟨fun _ => Set.univ⟩ : Frame (Fin 1)))
    have := hR.refl (∅ : Set (Fin 1)) (show (0 : Fin 1) ∈ _ by simp [Frame.box])
    simp at this

theorem LogicET_ssubset_LogicET4 : @LogicET ℕ ⊂ LogicET4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four (.atom 0) ∈ @LogicET ℕ := h (ProvableHilbert.axm (Or.inr ⟨_, rfl⟩))
    let F : Frame (Fin 2) := ⟨fun x => match x with | 0 => {Set.univ} | 1 => {{1}}⟩
    haveI : F.IsReflexive := ⟨by
      intro X x
      match x with
      | 0 => intro hx; simp_all [Frame.box, F]
      | 1 => intro hx; simp_all [Frame.box, F]⟩
    have hT := isTransitive_of_valid_axiomFour (LogicET.sound hFour F)
    have h0 : (0 : Fin 2) ∈ F.box Set.univ := by simp [Frame.box, F]
    have h1 := hT.trans Set.univ h0
    simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero, id_eq,
      Frame.box, F, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.ext_iff] at h1
    have h2 := h1 1
    simp at h2
    have h3 : (0 : Fin 2) ∈ ({1} : Set (Fin 2)) := h2 ▸ Set.mem_univ 0
    simp at h3

end
