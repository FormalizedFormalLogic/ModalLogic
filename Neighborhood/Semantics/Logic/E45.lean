module

public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Logic.E5
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_79

/-!
# The neighborhood logic `LogicE45`

Soundness and consistency of `LogicE45`, the classical modal logic axiomatised by the
transitivity axiom `Four` and the euclidean axiom `Five`, with respect to the transitive
and euclidean neighborhood frames.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicE45

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicE45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
theorem consistent : (@LogicE45 α).IsConsistent := by
  by_contra! hC
  simpa using LogicE45.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicE45 α)) :=
  MaximalConsistentSet.nonempty LogicE45.consistent

end LogicE45

theorem LogicE4_ssubset_LogicE45 : @LogicE4 ℕ ⊂ LogicE45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicE4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomFive
      (LogicE4.sound frame_1_0 hFive)

theorem LogicE5_ssubset_LogicE45 : @LogicE5 ℕ ⊂ LogicE45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicE5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_79.not_valid_axiomFour
      (LogicE5.sound frame_2_79 hFour)

end
