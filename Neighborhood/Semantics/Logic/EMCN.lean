module

public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Logic.EMC
public import Neighborhood.Semantics.Logic.EMN
public import Neighborhood.Semantics.Example.Frame2_153
public import Neighborhood.Semantics.Example.Frame2_206
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0

/-!
# The neighborhood logic `LogicEMCN`

Soundness, consistency and completeness of `LogicEMCN`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C` and `N := □⊤`, with respect to the
neighborhood frames that are monotonic, regular, and contain their unit.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMCN.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.ContainsUnit] :
    A ∈ LogicEMCN → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) <;> simp)

instance : (@LogicEMCN α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCN.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem LogicEMCN.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsRegular] →
      [F.ContainsUnit] → F ⊧ A) :
    A ∈ @LogicEMCN α :=
  (supplementedBasicCanonicalModel LogicEMCN).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMCN).toFrame
      (supplementedBasicCanonicalModel LogicEMCN).Val)

theorem LogicECN_ssubset_LogicEMCN : @LogicECN ℕ ⊂ LogicEMCN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hM : Axioms.M #0 #1 ∈ @LogicECN ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_153.not_valid_axiomM
      (LogicECN.sound frame_2_153 hM)


theorem LogicEMC_ssubset_LogicEMCN : @LogicEMC ℕ ⊂ LogicEMCN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEMC ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicEMC.sound frame_1_0 hN)

theorem LogicEMN_ssubset_LogicEMCN : @LogicEMN ℕ ⊂ LogicEMCN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicEMN ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_206.not_valid_axiomC
      (LogicEMN.sound frame_2_206 hC)

end
