module

public import Neighborhood.Semantics.Logic.EMCN
public import Neighborhood.Semantics.Logic.EMN
public import Neighborhood.Semantics.Logic.EMD
public import Neighborhood.Semantics.Logic.EMCD
public import Neighborhood.Semantics.Logic.ECND
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_206
public import Neighborhood.Semantics.Example.Frame3_9471106

/-!
# The neighborhood logic `LogicEMCND`

Soundness and consistency of `LogicEMCND`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C`, `N := □⊤`, and the seriality axiom `D`
over `LogicE`, with respect to the neighborhood frames that are monotonic, regular,
contain their unit, and are serial.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMCND.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.ContainsUnit] [F.IsSerial] :
    A ∈ LogicEMCND → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCND α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCND.sound frame_1_2 hC⟩

theorem LogicEMCN_ssubset_LogicEMCND : @LogicEMCN ℕ ⊂ LogicEMCND := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEMCN ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEMCN.sound frame_1_3 hD)

theorem LogicEMCD_ssubset_LogicEMCND : @LogicEMCD ℕ ⊂ LogicEMCND := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEMCD ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicEMCD.sound frame_1_0 hN)

theorem LogicECND_ssubset_LogicEMCND : @LogicECND ℕ ⊂ LogicEMCND := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hM : Axioms.M #0 #1 ∈ @LogicECND ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_9471106.not_valid_axiomM (LogicECND.sound frame_3_9471106 hM)

end
