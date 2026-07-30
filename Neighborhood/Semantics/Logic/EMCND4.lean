module

public import Neighborhood.Semantics.Logic.EMCN4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3

/-!
# The neighborhood logic `LogicEMCND4`

Soundness, consistency and the Nonempty instance for maximal consistent sets of `LogicEMCND4`,
the classical modal logic axiomatised by the monotonicity axiom `M`, the regularity axiom `C`,
`N := □⊤`, the seriality axiom `D` and the transitivity axiom `Four`, with respect to the
neighborhood frames that are monotonic, regular, transitive, serial and contain their unit.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMCND4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.ContainsUnit] [F.IsTransitive] [F.IsSerial] :
    A ∈ LogicEMCND4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMCND4.consistent : (@LogicEMCND4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMCND4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMCND4 α)) :=
  MaximalConsistentSet.nonempty LogicEMCND4.consistent

theorem LogicEMCN4_ssubset_LogicEMCND4 : @LogicEMCN4 ℕ ⊂ LogicEMCND4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ (@LogicEMCN4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEMCN4.sound frame_1_3 hD)

end
