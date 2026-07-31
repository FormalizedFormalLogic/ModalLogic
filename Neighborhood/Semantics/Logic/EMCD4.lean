module

public import Neighborhood.Semantics.Logic.EMC4

/-!
# The neighborhood logic `LogicEMCD4`

Soundness and consistency of `LogicEMCD4`,
the classical modal logic axiomatised by the monotonicity axiom `M`, the regularity axiom `C`,
the seriality axiom `D` and the transitivity axiom `Four`, with respect to the neighborhood
frames that are monotonic, regular, transitive and serial.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCD4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.IsTransitive] [F.IsSerial] :
    A ∈ LogicEMCD4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCD4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCD4.sound frame_1_2 hC⟩

end LogicEMCD4

theorem LogicEMC4_ssubset_LogicEMCD4 : @LogicEMC4 ℕ ⊂ LogicEMCD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMC4.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
