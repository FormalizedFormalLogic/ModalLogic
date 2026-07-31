module

public import Neighborhood.Semantics.Logic.ET
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame3_168

/-!
# The neighborhood logic `LogicECT`

Soundness and consistency of `LogicECT`, the classical modal logic axiomatised by the regularity
axiom `C` and the reflexivity axiom `T`, with respect to the regular and reflexive neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsReflexive] :
    A ∈ LogicECT → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECT.sound frame_1_2 hC⟩

end LogicECT

theorem LogicET_ssubset_LogicECT : @LogicET ℕ ⊂ LogicECT := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicET ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_168.not_valid_axiomC (LogicET.sound frame_3_168 hC)

end
