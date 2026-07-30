module

public import Neighborhood.Semantics.Logic.EMCN
public import Neighborhood.Semantics.Logic.E4
import Neighborhood.Semantics.Example.Frame1_2

/-!
# The neighborhood logic `LogicEMCN4`

Soundness, consistency and completeness of `LogicEMCN4`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C`, `N := □⊤` and the transitivity axiom `Four`,
with respect to the neighborhood frames that are monotonic, regular, transitive, and contain their
unit, together with its finite frame property.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMCN4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.ContainsUnit] [F.IsTransitive] :
    A ∈ LogicEMCN4 → F ⊧ A :=
  Hilbert.sound (by
    rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩)
    · exact valid_axiomM_of_isMonotonic
    · exact valid_axiomC_of_isRegular
    · exact valid_axiomN_of_containsUnit
    · exact valid_axiomFour_of_isTransitive)

theorem LogicEMCN4.consistent : (@LogicEMCN4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMCN4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMCN4 α)) :=
  MaximalConsistentSet.nonempty LogicEMCN4.consistent

variable [DecidableEq α]

theorem LogicEMCN4.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsRegular] →
      [F.ContainsUnit] → [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMCN4 α :=
  (supplementedBasicCanonicity LogicEMCN4).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMCN4).toModel.toFrame
      (supplementedBasicCanonicity LogicEMCN4).toModel.Val)

instance : FormulaSet.IsSubformulaClosed
    ((A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas) where
  closed B hB C hC := by
    rcases hB with hB | hB
    · exact Or.inl (Formula.subformulas.subset_of_mem hB hC)
    · exact Or.inr (Formula.subformulas.subset_of_mem hB hC)

theorem LogicEMCN4.finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.IsMonotonic] → [F.IsRegular] →
      [F.ContainsUnit] → [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMCN4 α :=
  LogicEMCN4.complete <| by
    intro κ _ F hMono hReg hUnit hTrans V x
    let M : Model κ α := ⟨F, V⟩
    let T : FormulaSet α := (A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas
    have hfin : T.Finite := by simp [T]
    haveI : Finite (FilterEqvQuotient M T) := FilterEqvQuotient.finite hfin
    haveI := quasiFilteringTransitiveFiltration.containsUnit (M := M) (T := T)
      (T_finite := hfin) (by simp [T])
    apply (quasiFilteringTransitiveFiltration M T hfin).filtration_satisfies _
      (by simp [T]) |>.mp
    haveI : (quasiFilteringTransitiveFiltration M T hfin).toModel.toFrame.IsFinite :=
      ⟨‹_›⟩
    exact h (quasiFilteringTransitiveFiltration M T hfin).toModel.toFrame
      (quasiFilteringTransitiveFiltration M T hfin).toModel.Val ⟦x⟧

end
