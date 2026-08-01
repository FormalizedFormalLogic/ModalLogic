module

public import Neighborhood.Logic.Logic.EMC
public import Neighborhood.Logic.Logic.EC4
public import Neighborhood.Logic.Logic.EM4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMC4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.IsTransitive] :
    A ∈ LogicEMC4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMC4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMC4.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsRegular] → [F.IsTransitive] →
      F ⊧ A) : A ∈ @LogicEMC4 α :=
  (supplementedBasicCanonicalModel LogicEMC4).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMC4).toFrame
      (supplementedBasicCanonicalModel LogicEMC4).Val)

theorem finite_complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.IsMonotonic] → [F.IsRegular] →
      [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMC4 α :=
  LogicEMC4.complete <| by
    intro κ _ F hMono hReg hTrans V x
    let M : Model κ α := ⟨F, V⟩
    have hfin : (A.subformulas : Set (Formula α)).Finite := by simp
    haveI : Finite (FilterEqvQuotient M A.subformulas) := FilterEqvQuotient.finite hfin
    apply (quasiFilteringTransitiveFiltration M A.subformulas hfin).filtration_satisfies _
      (by grind) |>.mp
    haveI : (quasiFilteringTransitiveFiltration M A.subformulas hfin).toModel.toFrame.IsFinite :=
      ⟨‹_›⟩
    exact h (quasiFilteringTransitiveFiltration M A.subformulas hfin).toModel.toFrame
      (quasiFilteringTransitiveFiltration M A.subformulas hfin).toModel.Val ⟦x⟧

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMC4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMC4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMC4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMC4.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMC4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMC4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMC4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMC4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMC4 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMC4.sound frame_1_3 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMC4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMC4.sound frame_1_0 (hcon #a))

theorem ssubset_LogicEMC : @LogicEMC ℕ ⊂ LogicEMC4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEMC.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEM4 : @LogicEM4 ℕ ⊂ LogicEMC4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEM4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEC4 : @LogicEC4 ℕ ⊂ LogicEMC4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEC4.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMC4

end
