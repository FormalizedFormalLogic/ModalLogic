module

public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Logic.EMC
public import Neighborhood.Semantics.Logic.EMN
import Neighborhood.Semantics.Example.ECNCounterframeForM
import Neighborhood.Semantics.Example.CounterframeAxiomC1
import Neighborhood.Semantics.Example.SimpleBlackhole
import Neighborhood.Semantics.Example.SimpleWhitehole

/-!
# The neighborhood logic `LogicEMCN`

Soundness, consistency and completeness of `LogicEMCN`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C` and `N := □⊤`, with respect to the
neighborhood frames that are monotonic, regular, and contain their unit.

Also proves the strict inclusions of `LogicECN`, `LogicEMC` and `LogicEMN` in `LogicEMCN` (a
comparison of two logics lives in the stronger logic's module).
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMCN.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.ContainsUnit] :
    A ∈ LogicEMCN → F ⊧ A :=
  Hilbert.sound (by
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl)
    · exact valid_axiomM_of_isMonotonic
    · exact valid_axiomC_of_isRegular
    · exact valid_axiomN_of_containsUnit)

theorem LogicEMCN.consistent : (@LogicEMCN α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMCN.sound Frame.simple_blackhole hC

instance : Nonempty (MaximalConsistentSet (@LogicEMCN α)) :=
  MaximalConsistentSet.nonempty LogicEMCN.consistent

variable [DecidableEq α]

theorem LogicEMCN.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsRegular] →
      [F.ContainsUnit] → F ⊧ A) :
    A ∈ @LogicEMCN α :=
  (supplementedBasicCanonicity LogicEMCN).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMCN).toModel.toFrame
      (supplementedBasicCanonicity LogicEMCN).toModel.Val)

theorem LogicECN_ssubset_LogicEMCN : @LogicECN ℕ ⊂ LogicEMCN := by
  constructor
  · apply Hilbert.subset_of_subset_axioms
    rintro A (hC | hN)
    · exact Or.inl (Or.inr hC)
    · exact Or.inr hN
  · intro h
    have hM : Axioms.M (.atom 0) (.atom 1) ∈ @LogicECN ℕ :=
      h (ProvableHilbert.axm (Or.inl (Or.inl ⟨_, _, rfl⟩)))
    exact Frame.ECN_counterframe_for_M.not_valid_axiomM
      (LogicECN.sound Frame.ECN_counterframe_for_M hM)


theorem LogicEMC_ssubset_LogicEMCN : @LogicEMC ℕ ⊂ LogicEMCN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEMC ℕ := h (ProvableHilbert.axm (Or.inr rfl))
    exact Frame.simple_whitehole.not_valid_axiomN (LogicEMC.sound Frame.simple_whitehole hN)

theorem LogicEMN_ssubset_LogicEMCN : @LogicEMN ℕ ⊂ LogicEMCN := by
  constructor
  · apply Hilbert.subset_of_subset_axioms
    rintro A (hM | hN)
    · exact Or.inl (Or.inl hM)
    · exact Or.inr hN
  · intro h
    have hC : Axioms.C (.atom 0) (.atom 1) ∈ @LogicEMN ℕ :=
      h (ProvableHilbert.axm (Or.inl (Or.inr ⟨_, _, rfl⟩)))
    exact Frame.counterframe_axiomC₁.not_valid_axiomC
      (LogicEMN.sound Frame.counterframe_axiomC₁ hC)

end
