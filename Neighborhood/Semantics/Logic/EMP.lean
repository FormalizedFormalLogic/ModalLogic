module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Logic.EP
public import Neighborhood.Semantics.Supplementation
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_78

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEMP.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.NotContainsEmpty] :
    A ∈ LogicEMP → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

theorem LogicEMP.consistent : (@LogicEMP α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMP.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMP α)) :=
  MaximalConsistentSet.nonempty LogicEMP.consistent

variable [DecidableEq α]

theorem LogicEMP.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicEMP α :=
  (supplementedBasicCanonicity LogicEMP).mem_of_valid
    (h (supplementedBasicCanonicity LogicEMP).toModel.toFrame
      (supplementedBasicCanonicity LogicEMP).toModel.Val)

theorem LogicEM_ssubset_LogicEMP : @LogicEM ℕ ⊂ LogicEMP := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hP : (Axioms.P : Formula ℕ) ∈ @LogicEM ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomP (LogicEM.sound frame_1_3 hP)

theorem LogicEP_ssubset_LogicEMP : @LogicEP ℕ ⊂ LogicEMP := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hM : (Axioms.M #0 #1 : Formula ℕ) ∈ @LogicEP ℕ := h (Logic.HasAxiomM.M _ _)
    exact frame_2_78.not_valid_axiomM (LogicEP.sound frame_2_78 hM)

end
