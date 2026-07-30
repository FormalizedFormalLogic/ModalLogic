module

public import Neighborhood.Semantics.Logic.EMT4
public import Neighborhood.Semantics.Logic.EMN
public import Neighborhood.Semantics.Logic.ENT4
public import Neighborhood.Semantics.Filtration

/-!
# The neighborhood logic `LogicEMNT4`

Soundness, consistency and completeness of `LogicEMNT4`, the classical modal logic axiomatised by
the monotonicity axiom `M`, `N := □⊤`, the reflexivity axiom `T` and the transitivity axiom `Four`,
with respect to the neighborhood frames that are monotonic, contain their unit, are reflexive and
are transitive, together with its finite frame property.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMNT4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.ContainsUnit] [F.IsReflexive] [F.IsTransitive] :
    A ∈ LogicEMNT4 → F ⊧ A :=
  Hilbert.sound (by
    rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩)
    · exact valid_axiomM_of_isMonotonic
    · exact valid_axiomN_of_containsUnit
    · exact valid_axiomT_of_isReflexive
    · exact valid_axiomFour_of_isTransitive)

theorem LogicEMNT4.consistent : (@LogicEMNT4 α).IsConsistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole) (by
    rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩)
    · exact valid_axiomM_of_isMonotonic
    · exact valid_axiomN_of_containsUnit
    · exact valid_axiomT_of_isReflexive
    · exact valid_axiomFour_of_isTransitive)

instance : Nonempty (MaximalConsistentSet (@LogicEMNT4 α)) :=
  MaximalConsistentSet.nonempty LogicEMNT4.consistent

variable [DecidableEq α]

theorem LogicEMNT4.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] →
      [F.IsReflexive] → [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMNT4 α :=
  (supplementedBasicCanonicity LogicEMNT4).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMNT4).toModel.toFrame
      (supplementedBasicCanonicity LogicEMNT4).toModel.Val)

theorem LogicEMNT4.finite_complete
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

end
