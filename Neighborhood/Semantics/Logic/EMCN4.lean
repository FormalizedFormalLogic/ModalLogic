module

public import Neighborhood.Semantics.Logic.EMCN
public import Neighborhood.Semantics.Logic.EMC4

/-!
# The neighborhood logic `LogicEMCN4`

Soundness, consistency and completeness of `LogicEMCN4`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C`, `N := □⊤` and the transitivity axiom `Four`,
with respect to the neighborhood frames that are monotonic, regular, transitive, and contain their
unit, together with its finite frame property.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCN4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.ContainsUnit] [F.IsTransitive] :
    A ∈ LogicEMCN4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCN4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCN4.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsRegular] →
      [F.ContainsUnit] → [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMCN4 α :=
  (supplementedBasicCanonicalModel LogicEMCN4).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMCN4).toFrame
      (supplementedBasicCanonicalModel LogicEMCN4).Val)

instance : FormulaSet.IsSubformulaClosed
    ((A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas) where
  closed B hB C hC := by
    rcases hB with hB | hB
    · exact Or.inl (Formula.subformulas.subset_of_mem hB hC)
    · exact Or.inr (Formula.subformulas.subset_of_mem hB hC)

theorem finite_complete
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

omit [DecidableEq α] in
lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMCN4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMCN4.sound frame_1_3 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCN4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEMCN4.sound frame_2_138 (hcon #a))

end LogicEMCN4

theorem LogicEMC4_ssubset_LogicEMCN4 : @LogicEMC4 ℕ ⊂ LogicEMCN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEMC4.not_provable_axiomN⟩

theorem LogicEMCN_ssubset_LogicEMCN4 : @LogicEMCN ℕ ⊂ LogicEMCN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMCN.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

end
