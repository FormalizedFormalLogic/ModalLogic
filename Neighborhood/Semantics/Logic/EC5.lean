module

public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Logic.E5
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame3_10528928

/-!
# The neighborhood logic `LogicEC5`

Soundness and consistency of `LogicEC5`, the classical
modal logic axiomatised by the regularity axiom `C` and the Euclideanness axiom `Five`
over `LogicE`, with respect to the regular and Euclidean neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEC5.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsEuclidean] :
    A ∈ LogicEC5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEC5.consistent : (@LogicEC5 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEC5.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEC5 α)) :=
  MaximalConsistentSet.nonempty LogicEC5.consistent

theorem LogicEC_ssubset_LogicEC5 : (@LogicEC ℕ) ⊂ LogicEC5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEC ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomFive (LogicEC.sound frame_1_0 hFive)

theorem LogicE5_ssubset_LogicEC5 : (@LogicE5 ℕ) ⊂ LogicEC5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hC : Axioms.C #0 #1 ∈ (@LogicE5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_10528928.not_valid_axiomC (LogicE5.sound frame_3_10528928 hC)

end
