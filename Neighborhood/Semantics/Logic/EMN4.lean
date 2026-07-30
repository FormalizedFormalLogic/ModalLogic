module

public import Neighborhood.Semantics.Logic.EM4
public import Neighborhood.Semantics.Logic.EMN
public import Neighborhood.Semantics.Logic.EN4
public import Neighborhood.Semantics.Filtration
public import Neighborhood.Semantics.Example.Frame1_2

/-!
# The neighborhood logic `LogicEMN4`

Soundness, consistency and completeness of `LogicEMN4`, the classical modal logic axiomatised by
the monotonicity axiom `M`, `N := □⊤` and the transitivity axiom `Four`, with respect to the
neighborhood frames that are monotonic, contain their unit and are transitive, together with its
finite frame property.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMN4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.ContainsUnit] [F.IsTransitive] :
    A ∈ LogicEMN4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMN4.consistent : (@LogicEMN4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMN4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMN4 α)) :=
  MaximalConsistentSet.nonempty LogicEMN4.consistent

variable [DecidableEq α]

theorem LogicEMN4.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] →
      [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMN4 α :=
  (supplementedBasicCanonicity LogicEMN4).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMN4).toModel.toFrame
      (supplementedBasicCanonicity LogicEMN4).toModel.Val)

theorem LogicEMN4.finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.IsMonotonic] →
      [F.ContainsUnit] → [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMN4 α :=
  LogicEMN4.complete <| by
    intro κ _ F hMono hUnit hTrans V x
    let M : Model κ α := ⟨F, V⟩
    let T : FormulaSet α := (A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas
    haveI : Finite (FilterEqvQuotient M T) := FilterEqvQuotient.finite (by simp [T])
    haveI := supplementedTransitiveFiltration.containsUnit (M := M) (T := T) (by simp [T])
    apply (supplementedTransitiveFiltration M T).filtration_satisfies _ (by simp [T]) |>.mp
    haveI : (supplementedTransitiveFiltration M T).toModel.toFrame.IsFinite := ⟨‹_›⟩
    exact h (supplementedTransitiveFiltration M T).toModel.toFrame
      (supplementedTransitiveFiltration M T).toModel.Val ⟦x⟧

end
