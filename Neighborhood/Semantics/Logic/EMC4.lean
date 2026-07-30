module

public import Neighborhood.Semantics.Logic.EMC
public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Filtration

/-!
# The neighborhood logic `LogicEMC4`

Soundness, consistency and completeness of `LogicEMC4`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C` and the transitivity axiom `Four`, with
respect to the neighborhood frames that are monotonic, regular and transitive, together with its
finite frame property. Also proves the strict inclusion of `LogicEMC` in `LogicEMC4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMC4.sound (h : A ∈ LogicEMC4) {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.IsTransitive] : F ⊧ A :=
  Hilbert.sound (by
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩)
    · exact valid_axiomM_of_isMonotonic
    · exact valid_axiomC_of_isRegular
    · exact valid_axiomFour_of_isTransitive) h

instance : (@LogicEMC4 α).Consistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole) (by
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩)
    · exact valid_axiomM_of_isMonotonic
    · exact valid_axiomC_of_isRegular
    · exact valid_axiomFour_of_isTransitive)

variable [DecidableEq α]

theorem LogicEMC4.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.IsMonotonic → F.IsRegular → F.IsTransitive →
      F ⊧ A) : A ∈ @LogicEMC4 α :=
  (supplementedBasicCanonicity LogicEMC4).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMC4).toModel.toFrame inferInstance inferInstance
      inferInstance (supplementedBasicCanonicity LogicEMC4).toModel.Val)

theorem LogicEMC4.finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.IsFinite → F.IsMonotonic → F.IsRegular →
      F.IsTransitive → F ⊧ A) : A ∈ @LogicEMC4 α :=
  LogicEMC4.complete <| by
    intro κ _ F hMono hReg hTrans V x
    let M : Model κ α := ⟨F, V⟩
    haveI : Finite (FilterEqvQuotient M A.subformulas) := FilterEqvQuotient.finite (by simp)
    apply (quasiFilteringTransitiveFiltration M A.subformulas (by simp)).filtration_satisfies _
      (by grind) |>.mp
    exact h (quasiFilteringTransitiveFiltration M A.subformulas (by simp)).toModel.toFrame ⟨‹_›⟩
      quasiFilteringTransitiveFiltration.isMonotonic quasiFilteringTransitiveFiltration.isRegular
      quasiFilteringTransitiveFiltration.isTransitive
      (quasiFilteringTransitiveFiltration M A.subformulas (by simp)).toModel.Val ⟦x⟧


theorem LogicEMC_ssubset_LogicEMC4 : @LogicEMC ℕ ⊂ LogicEMC4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four (.atom 0) ∈ (@LogicEMC ℕ) := h (ProvableHilbert.axm (Or.inr ⟨_, rfl⟩))
    exact Frame.trivial_nontransitive.not_valid_axiomFour
      (LogicEMC.sound hFour Frame.trivial_nontransitive)

end
