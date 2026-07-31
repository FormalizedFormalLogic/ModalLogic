module

public import Neighborhood.Semantics.Logic.EMC
public import Neighborhood.Semantics.Logic.EMD
public import Neighborhood.Semantics.Logic.ECP
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_34
public import Neighborhood.Semantics.Example.Frame3_10528928

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

instance : (@LogicEMCD α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCD.sound frame_1_2 hC⟩

theorem LogicEMC_ssubset_LogicEMCD : @LogicEMC ℕ ⊂ LogicEMCD := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEMC ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEMC.sound frame_1_3 hD)

theorem LogicEMD_ssubset_LogicEMCD : @LogicEMD ℕ ⊂ LogicEMCD := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.union_subset_union_left _ Set.subset_union_left)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicEMD ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_10528928.not_valid_axiomC (LogicEMD.sound frame_3_10528928 hC)

theorem LogicECP_ssubset_LogicEMCD : @LogicECP ℕ ⊂ LogicEMCD := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, C, rfl⟩ | rfl) <;> first | exact Logic.axiomC | exact Logic.axiomP_of_MD
  · intro h
    have hM : Axioms.M #0 #1 ∈ @LogicECP ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_34.not_valid_axiomM (LogicECP.sound frame_2_34 hM)

end
