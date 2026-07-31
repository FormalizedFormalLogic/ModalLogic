module

public import Neighborhood.Semantics.Logic.EMCD5
public import Neighborhood.Semantics.Logic.EMCND4
public import Neighborhood.Semantics.Logic.EMC45
public import Neighborhood.Semantics.Logic.EMD45
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_10529440
public import Neighborhood.Semantics.Example.Frame3_11053224

/-!
# The neighborhood logic `LogicEMCD45`

Soundness and consistency of `LogicEMCD45`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the regularity axiom `C`, the seriality axiom `D`, the transitivity axiom
`Four` and the euclideanness axiom `Five`, with respect to the neighborhood frames that are
monotonic, regular, serial, transitive and euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMCD45.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsSerial] [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicEMCD45 → F ⊧ A :=
  Hilbert.sound (by
    rintro _ ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMCD45.consistent : (@LogicEMCD45 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMCD45.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMCD45 α)) :=
  MaximalConsistentSet.nonempty LogicEMCD45.consistent

theorem LogicEMCD5_ssubset_LogicEMCD45 : @LogicEMCD5 ℕ ⊂ LogicEMCD45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicEMCD5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_10529440.not_valid_axiomFour (LogicEMCD5.sound frame_3_10529440 hFour)

theorem LogicEMCND4_ssubset_LogicEMCD45 : @LogicEMCND4 ℕ ⊂ LogicEMCD45 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD |
        exact Logic.axiomFour
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEMCND4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomFive (LogicEMCND4.sound frame_2_138 hFive)

theorem LogicEMC45_ssubset_LogicEMCD45 : @LogicEMC45 ℕ ⊂ LogicEMCD45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ (@LogicEMC45 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEMC45.sound frame_1_3 hD)

theorem LogicEMD45_ssubset_LogicEMCD45 : @LogicEMD45 ℕ ⊂ LogicEMCD45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicEMD45 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_11053224.not_valid_axiomC (LogicEMD45.sound frame_3_11053224 hC)

end
