module

public import Neighborhood.Semantics.Logic.EMC
public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Logic.EC4
public import Neighborhood.Semantics.Logic.EM4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame2_206
public import Neighborhood.Semantics.Example.Frame3_9471106

/-!
# The neighborhood logic `LogicEMC4`

Soundness, consistency and completeness of `LogicEMC4`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C` and the transitivity axiom `Four`, with
respect to the neighborhood frames that are monotonic, regular and transitive, together with its
finite frame property.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMC4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.IsTransitive] :
    A ∈ LogicEMC4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMC4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMC4.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem LogicEMC4.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsRegular] → [F.IsTransitive] →
      F ⊧ A) : A ∈ @LogicEMC4 α :=
  (supplementedBasicCanonicalModel LogicEMC4).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMC4).toFrame
      (supplementedBasicCanonicalModel LogicEMC4).Val)

theorem LogicEMC4.finite_complete
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


theorem LogicEMC_ssubset_LogicEMC4 : @LogicEMC ℕ ⊂ LogicEMC4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicEMC ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_8.not_valid_axiomFour
      (LogicEMC.sound frame_2_8 hFour)

theorem LogicEM4_ssubset_LogicEMC4 : @LogicEM4 ℕ ⊂ LogicEMC4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ (@LogicEM4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_206.not_valid_axiomC
      (LogicEM4.sound frame_2_206 hC)

theorem LogicEC4_ssubset_LogicEMC4 : @LogicEC4 ℕ ⊂ LogicEMC4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicEC4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_9471106.not_valid_axiomM (LogicEC4.sound frame_3_9471106 hM)

end
