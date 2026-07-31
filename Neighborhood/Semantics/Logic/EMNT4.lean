module

public import Neighborhood.Semantics.Logic.EMT4
public import Neighborhood.Semantics.Logic.EMN
public import Neighborhood.Semantics.Logic.ENT4

/-!
# The neighborhood logic `LogicEMNT4`

Soundness, consistency and completeness of `LogicEMNT4`, the classical modal logic axiomatised by
the monotonicity axiom `M`, `N := □⊤`, the reflexivity axiom `T` and the transitivity axiom `Four`,
with respect to the neighborhood frames that are monotonic, contain their unit, are reflexive and
are transitive, together with its finite frame property.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMNT4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.ContainsUnit] [F.IsReflexive] [F.IsTransitive] :
    A ∈ LogicEMNT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMNT4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMNT4.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] →
      [F.IsReflexive] → [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMNT4 α :=
  (supplementedBasicCanonicalModel LogicEMNT4).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMNT4).toFrame
      (supplementedBasicCanonicalModel LogicEMNT4).Val)

theorem finite_complete
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

end LogicEMNT4

theorem LogicEMT4_ssubset_LogicEMNT4 : @LogicEMT4 ℕ ⊂ LogicEMNT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEMT4.not_provable_axiomN⟩

theorem LogicENT4_ssubset_LogicEMNT4 : @LogicENT4 ℕ ⊂ LogicEMNT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicENT4.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
