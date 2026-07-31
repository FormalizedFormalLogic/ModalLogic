module

public import Neighborhood.Semantics.Logic.EMT
public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Logic.ECT
public import Neighborhood.Semantics.Logic.EMCD
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_168
public import Neighborhood.Semantics.Example.Frame3_9471106

/-!
# The neighborhood logic `LogicEMCT`

Soundness and consistency of `LogicEMCT`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C`, and the reflexivity axiom `T`,
with respect to the neighborhood frames that are monotonic, regular, and reflexive.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsReflexive] :
    A ∈ LogicEMCT → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCT.sound frame_1_2 hC⟩

end LogicEMCT

theorem LogicEMT_ssubset_LogicEMCT : @LogicEMT ℕ ⊂ LogicEMCT := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicEMT ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_168.not_valid_axiomC (LogicEMT.sound frame_3_168 hC)

theorem LogicECT_ssubset_LogicEMCT : @LogicECT ℕ ⊂ LogicEMCT := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hM : Axioms.M #0 #1 ∈ @LogicECT ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_9471106.not_valid_axiomM (LogicECT.sound frame_3_9471106 hM)

theorem LogicEMCD_ssubset_LogicEMCT : @LogicEMCD ℕ ⊂ LogicEMCT := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩)
    · exact ProvableHilbert.axm (by grind)
    · exact ProvableHilbert.axm (by grind)
    · exact Logic.axiomD
  · intro h
    have hT : Axioms.T #0 ∈ @LogicEMCD ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomT (LogicEMCD.sound frame_2_170 hT)

end
