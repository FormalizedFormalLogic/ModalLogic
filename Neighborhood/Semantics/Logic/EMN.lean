module

public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_137

/-!
# The neighborhood logic `LogicEMN`

Soundness, consistency and completeness of `LogicEMN`, the classical modal logic axiomatised by
the monotonicity axiom `M` together with `N := □⊤`, with respect to the monotonic frames
containing their unit.

Also proves the strict inclusions of `LogicEM` and `LogicEN` in `LogicEMN` (a comparison of two
logics lives in the stronger logic's module).
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMN.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.ContainsUnit] :
    A ∈ LogicEMN → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

theorem LogicEMN.consistent : (@LogicEMN α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMN.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMN α)) :=
  MaximalConsistentSet.nonempty LogicEMN.consistent

variable [DecidableEq α]

theorem LogicEMN.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] → F ⊧ A) :
    A ∈ @LogicEMN α :=
  (supplementedBasicCanonicity LogicEMN).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMN).toModel.toFrame
      (supplementedBasicCanonicity LogicEMN).toModel.Val)

theorem LogicEM_ssubset_LogicEMN : @LogicEM ℕ ⊂ LogicEMN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEM ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicEM.sound frame_1_0 hN)

theorem LogicEN_ssubset_LogicEMN : @LogicEN ℕ ⊂ LogicEMN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicEN ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_137.not_valid_axiomM (LogicEN.sound _ hM)

end
