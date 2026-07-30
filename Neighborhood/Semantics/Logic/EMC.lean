module

public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Logic.EK
import Neighborhood.Semantics.Example.EKCounterframeForMAndC
import Neighborhood.Semantics.Example.CounterframeAxiomC1
import Neighborhood.Semantics.Example.CounterframeAxiomM1
import Neighborhood.Semantics.Example.SimpleBlackhole

/-!
# The neighborhood logic `LogicEMC`

Soundness, consistency and completeness of `LogicEMC`, the classical modal logic axiomatised by
the monotonicity axiom `M` and the regularity axiom `C`, with respect to the neighborhood frames
that are both monotonic and regular, and its strict inclusion of `LogicEM`, `LogicEC` and
`LogicEK`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMC.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] :
    A ∈ LogicEMC → F ⊧ A :=
  Hilbert.sound (by
    rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩)
    · exact valid_axiomM_of_isMonotonic
    · exact valid_axiomC_of_isRegular)

theorem LogicEMC.consistent : (@LogicEMC α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMC.sound Frame.simple_blackhole hC

instance : Nonempty (MaximalConsistentSet (@LogicEMC α)) :=
  MaximalConsistentSet.nonempty LogicEMC.consistent

variable [DecidableEq α]

theorem LogicEMC.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsRegular] → F ⊧ A) :
    A ∈ @LogicEMC α :=
  (supplementedBasicCanonicity LogicEMC).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMC).toModel.toFrame
      (supplementedBasicCanonicity LogicEMC).toModel.Val)

theorem LogicEM_ssubset_LogicEMC : @LogicEM ℕ ⊂ LogicEMC := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hC : Axioms.C (.atom 0) (.atom 1) ∈ @LogicEM ℕ :=
      h (ProvableHilbert.axm (Or.inr ⟨_, _, rfl⟩))
    exact Frame.counterframe_axiomC₁.not_valid_axiomC (LogicEM.sound Frame.counterframe_axiomC₁ hC)

theorem LogicEC_ssubset_LogicEMC : @LogicEC ℕ ⊂ LogicEMC := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hM : Axioms.M (.atom 0) (.atom 1) ∈ @LogicEC ℕ :=
      h (ProvableHilbert.axm (Or.inl ⟨_, _, rfl⟩))
    exact Frame.counterframe_axiomM₁.not_valid_axiomM (LogicEC.sound Frame.counterframe_axiomM₁ hM)

theorem LogicEK_ssubset_LogicEMC : @LogicEK ℕ ⊂ LogicEMC := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ⟨A, B, rfl⟩
    exact Logic.axiomK_of_MC
  · intro h
    have hC : Axioms.C (.atom 0) (.atom 1) ∈ @LogicEK ℕ :=
      h (ProvableHilbert.axm (Or.inr ⟨_, _, rfl⟩))
    exact Frame.EK_counterframe_for_M_and_C.not_valid_axiomC
      (LogicEK.sound Frame.EK_counterframe_for_M_and_C hC)

end
