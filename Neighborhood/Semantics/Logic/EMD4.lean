module

public import Neighborhood.Semantics.Logic.EM4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3

/-!
# The neighborhood logic `LogicEMD4`

Soundness, consistency and the Nonempty instance for maximal consistent sets of `LogicEMD4`,
the classical modal logic axiomatised by the monotonicity axiom `M`, the seriality axiom `D` and
the transitivity axiom `Four`, with respect to the neighborhood frames that are monotonic,
transitive and serial.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMD4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsTransitive] [F.IsSerial] :
    A ∈ LogicEMD4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMD4.consistent : (@LogicEMD4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMD4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMD4 α)) :=
  MaximalConsistentSet.nonempty LogicEMD4.consistent

theorem LogicEM4_ssubset_LogicEMD4 : @LogicEM4 ℕ ⊂ LogicEMD4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ (@LogicEM4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEM4.sound frame_1_3 hD)

end
