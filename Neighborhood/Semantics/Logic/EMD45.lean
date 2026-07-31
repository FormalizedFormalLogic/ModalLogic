module

public import Neighborhood.Semantics.Logic.END45
public import Neighborhood.Semantics.Logic.EMND4
public import Neighborhood.Semantics.Logic.EMD5
public import Neighborhood.Semantics.Logic.EM45
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame3_8553090
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_10528928
public import Neighborhood.Semantics.Example.Frame1_3

/-!
# The neighborhood logic `LogicEMD45`

Soundness and consistency of `LogicEMD45`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the seriality axiom `D`, the transitivity axiom `Four` and the euclidean
axiom `Five`, with respect to the neighborhood frames that are monotonic, serial, transitive and
euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMD45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSerial] [F.IsTransitive]
    [F.IsEuclidean] :
    A ∈ LogicEMD45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMD45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMD45.sound frame_1_2 hC⟩

end LogicEMD45

theorem LogicEND45_ssubset_LogicEMD45 : @LogicEND45 ℕ ⊂ LogicEMD45 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first
        | exact Logic.axiomN
        | exact Logic.axiomD
        | exact Logic.axiomFour
        | exact Logic.axiomFive
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicEND45 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_8553090.not_valid_axiomM (LogicEND45.sound frame_3_8553090 hM)

theorem LogicEMND4_ssubset_LogicEMD45 : @LogicEMND4 ℕ ⊂ LogicEMD45 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first
        | exact Logic.axiomM
        | exact Logic.axiomN
        | exact Logic.axiomD
        | exact Logic.axiomFour
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEMND4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomFive (LogicEMND4.sound frame_2_138 hFive)

theorem LogicEMD5_ssubset_LogicEMD45 : @LogicEMD5 ℕ ⊂ LogicEMD45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicEMD5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_10528928.not_valid_axiomFour (LogicEMD5.sound frame_3_10528928 hFour)

theorem LogicEM45_ssubset_LogicEMD45 : @LogicEM45 ℕ ⊂ LogicEMD45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ (@LogicEM45 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEM45.sound frame_1_3 hD)

end
