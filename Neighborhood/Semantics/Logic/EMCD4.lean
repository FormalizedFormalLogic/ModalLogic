module

public import Neighborhood.Semantics.Logic.EMC4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3

/-!
# The neighborhood logic `LogicEMCD4`

Soundness, consistency and the Nonempty instance for maximal consistent sets of `LogicEMCD4`,
the classical modal logic axiomatised by the monotonicity axiom `M`, the regularity axiom `C`,
the seriality axiom `D` and the transitivity axiom `Four`, with respect to the neighborhood
frames that are monotonic, regular, transitive and serial.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMCD4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.IsTransitive] [F.IsSerial] :
    A ∈ LogicEMCD4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCD4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCD4.sound frame_1_2 hC⟩

theorem LogicEMC4_ssubset_LogicEMCD4 : @LogicEMC4 ℕ ⊂ LogicEMCD4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ (@LogicEMC4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEMC4.sound frame_1_3 hD)

end
