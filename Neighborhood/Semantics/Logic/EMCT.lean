module

public import Neighborhood.Semantics.Logic.EMT
public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame3_168

/-!
# The neighborhood logic `LogicEMCT`

Soundness and consistency of `LogicEMCT`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C`, and the reflexivity axiom `T`,
with respect to the neighborhood frames that are monotonic, regular, and reflexive.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMCT.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsReflexive] :
    A ∈ LogicEMCT → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMCT.consistent : (@LogicEMCT α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMCT.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMCT α)) :=
  MaximalConsistentSet.nonempty LogicEMCT.consistent

theorem LogicEMT_ssubset_LogicEMCT : @LogicEMT ℕ ⊂ LogicEMCT := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicEMT ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_168.not_valid_axiomC (LogicEMT.sound frame_3_168 hC)

end
