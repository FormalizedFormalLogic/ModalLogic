module

public import Neighborhood.Semantics.Logic.EMCND
public import Neighborhood.Semantics.Logic.EMB
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame1_3

/-!
# The neighborhood logic `LogicEMDB`

Soundness and consistency of `LogicEMDB`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the seriality axiom `D`, and the symmetry axiom `B`, with respect to the
neighborhood frames that are monotonic, serial, and symmetric.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMDB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSerial]
    [F.IsSymmetric] :
    A ∈ LogicEMDB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMDB.sound frame_1_2 hC⟩

end LogicEMDB

theorem LogicEMCND_ssubset_LogicEMDB : @LogicEMCND ℕ ⊂ LogicEMDB := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD
  · intro h
    have hB : Axioms.B #0 ∈ (@LogicEMCND ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomB (LogicEMCND.sound frame_2_138 hB)

theorem LogicEMB_ssubset_LogicEMDB : @LogicEMB ℕ ⊂ LogicEMDB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEMB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEMB.sound frame_1_3 hD)

end
