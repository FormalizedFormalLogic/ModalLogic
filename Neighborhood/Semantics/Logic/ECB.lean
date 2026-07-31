module

public import Neighborhood.Semantics.Logic.EB
public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame3_9488552

/-!
# The neighborhood logic `LogicECB`

Soundness and consistency of `LogicECB`, the classical
modal logic axiomatised by the regularity axiom `C` and the symmetry axiom `B` over
`LogicE`, with respect to the regular and symmetric neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicECB.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSymmetric] :
    A ∈ LogicECB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicECB.consistent : (@LogicECB α).IsConsistent := by
  by_contra! hC
  simpa using LogicECB.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECB α)) :=
  MaximalConsistentSet.nonempty LogicECB.consistent

theorem LogicEC_ssubset_LogicECB : (@LogicEC ℕ) ⊂ LogicECB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hB : Axioms.B #0 ∈ (@LogicEC ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomB (LogicEC.sound frame_1_0 hB)

theorem LogicEB_ssubset_LogicECB : @LogicEB ℕ ⊂ LogicECB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicEB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_9488552.not_valid_axiomC (LogicEB.sound frame_3_9488552 hC)

end
