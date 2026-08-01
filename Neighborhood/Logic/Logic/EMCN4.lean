module

public import Neighborhood.Logic.Logic.EMCN
public import Neighborhood.Logic.Logic.EMC4

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

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsRegular] →
      [F.ContainsUnit] → [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMCN4 α :=
  (supplementedBasicCanonicalModel LogicEMCN4).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMCN4).toFrame
      (supplementedBasicCanonicalModel LogicEMCN4).Val)

instance [DecidableEq α] : FormulaSet.IsSubformulaClosed
    ((A.subformulas : Set (Formula α)) ∪ (□⊤ : Formula α).subformulas) where
  closed B hB C hC := by
    rcases hB with hB | hB
    · exact Or.inl (Formula.subformulas.subset_of_mem hB hC)
    · exact Or.inr (Formula.subformulas.subset_of_mem hB hC)

theorem finite_complete [DecidableEq α]
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

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMCN4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMCN4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCN4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEMCN4.sound frame_2_138 (hcon #a))

end LogicEMCN4

theorem LogicEMCN4.ssubset_LogicEMC4 : @LogicEMC4 ℕ ⊂ LogicEMCN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEMC4.not_provable_axiomN⟩

theorem LogicEMCN4.ssubset_LogicEMCN : @LogicEMCN ℕ ⊂ LogicEMCN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMCN.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

end
