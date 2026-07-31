module

public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame3_10520744

/-!
# The neighborhood logic `LogicEC4`

Soundness and consistency of `LogicEC4`, the classical
modal logic axiomatised by the regularity axiom `C` and the transitivity axiom `Four` over
`LogicE`, with respect to the regular and transitive neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEC4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsTransitive] :
    A ∈ LogicEC4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEC4.consistent : (@LogicEC4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEC4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEC4 α)) :=
  MaximalConsistentSet.nonempty LogicEC4.consistent

theorem LogicEC_ssubset_LogicEC4 : (@LogicEC ℕ) ⊂ LogicEC4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicEC ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_1.not_valid_axiomFour (LogicEC.sound frame_1_1 hFour)

theorem LogicE4_ssubset_LogicEC4 : @LogicE4 ℕ ⊂ LogicEC4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hC : Axioms.C #0 #1 ∈ (@LogicE4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_10520744.not_valid_axiomC (LogicE4.sound frame_3_10520744 hC)

end
