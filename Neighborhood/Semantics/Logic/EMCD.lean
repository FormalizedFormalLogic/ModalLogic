module

public import Neighborhood.Semantics.Logic.EMC
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3

/-!
# The neighborhood logic `LogicEMCD`

Soundness and consistency of `LogicEMCD`, the classical modal logic axiomatised by the monotonicity
axiom `M`, the regularity axiom `C`, and the seriality axiom `D`, with respect to the monotonic,
regular, and serial neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMCD.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsSerial] :
    A ∈ LogicEMCD → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMCD.consistent : (@LogicEMCD α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMCD.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMCD α)) :=
  MaximalConsistentSet.nonempty LogicEMCD.consistent

theorem LogicEMC_ssubset_LogicEMCD : @LogicEMC ℕ ⊂ LogicEMCD := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEMC ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEMC.sound frame_1_3 hD)

end
