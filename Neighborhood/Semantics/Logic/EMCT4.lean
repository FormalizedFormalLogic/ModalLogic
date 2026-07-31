module

public import Neighborhood.Semantics.Logic.EMT4
public import Neighborhood.Semantics.Logic.EMC4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame3_10520744

/-!
# The neighborhood logic `LogicEMCT4`

Soundness and consistency of `LogicEMCT4`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C`, the reflexivity axiom `T`, and
the transitivity axiom `Four`, with respect to the neighborhood frames that are monotonic,
regular, reflexive, and transitive.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMCT4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsReflexive] [F.IsTransitive] :
    A ∈ LogicEMCT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMCT4.consistent : (@LogicEMCT4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMCT4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMCT4 α)) :=
  MaximalConsistentSet.nonempty LogicEMCT4.consistent

theorem LogicEMT4_ssubset_LogicEMCT4 : @LogicEMT4 ℕ ⊂ LogicEMCT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicEMT4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_10520744.not_valid_axiomC (LogicEMT4.sound frame_3_10520744 hC)

end
