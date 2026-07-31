module

public import Neighborhood.Semantics.Logic.EMC
public import Neighborhood.Semantics.Logic.EC4
public import Neighborhood.Semantics.Logic.EM4

/-!
# The neighborhood logic `LogicEMC4`

Soundness, consistency and completeness of `LogicEMC4`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C` and the transitivity axiom `Four`, with
respect to the neighborhood frames that are monotonic, regular and transitive, together with its
finite frame property.
-/

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

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsRegular] → [F.IsTransitive] →
      F ⊧ A) : A ∈ @LogicEMC4 α :=
  (supplementedBasicCanonicalModel LogicEMC4).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMC4).toFrame
      (supplementedBasicCanonicalModel LogicEMC4).Val)

theorem finite_complete
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

omit [DecidableEq α] in
lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMC4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMC4.sound frame_1_3 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMC4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMC4.sound frame_1_0 hcon)

end LogicEMC4

theorem LogicEMC_ssubset_LogicEMC4 : @LogicEMC ℕ ⊂ LogicEMC4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEMC.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEM4_ssubset_LogicEMC4 : @LogicEM4 ℕ ⊂ LogicEMC4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEM4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEC4_ssubset_LogicEMC4 : @LogicEC4 ℕ ⊂ LogicEMC4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEC4.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
