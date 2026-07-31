module

public import Neighborhood.Semantics.Logic.EMC5
public import Neighborhood.Semantics.Logic.EMCND
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_140

/-!
# The neighborhood logic `LogicEMCD5`

Soundness and consistency of `LogicEMCD5`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the regularity axiom `C`, the seriality axiom `D` and the euclideanness
axiom `Five`, with respect to the neighborhood frames that are monotonic, regular, serial and
euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMCD5.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsSerial] [F.IsEuclidean] :
    A ∈ LogicEMCD5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCD5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCD5.sound frame_1_2 hC⟩

theorem LogicEMC5_ssubset_LogicEMCD5 : @LogicEMC5 ℕ ⊂ LogicEMCD5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEMC5 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEMC5.sound frame_1_3 hD)

theorem LogicEMCND_ssubset_LogicEMCD5 : @LogicEMCND ℕ ⊂ LogicEMCD5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEMCND ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomFive (LogicEMCND.sound frame_2_140 hFive)

end
