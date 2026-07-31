module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_79

/-!
# The neighborhood logic `LogicED`

Soundness and consistency of `LogicED`, the classical modal logic axiomatised by the seriality
axiom `D`, with respect to the serial neighborhood frames (`Frame.IsSerial`), and the strict
inclusion of `LogicE` in `LogicED`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicED

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] :
    A ∈ LogicED → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, rfl⟩; simp)

instance : (@LogicED α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicED.sound frame_1_2 hC⟩

end LogicED

theorem LogicE_ssubset_LogicED : @LogicE ℕ ⊂ LogicED := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hD : Axioms.D #0 ∈ @LogicE ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_79.not_isSerial (isSerial_of_valid_axiomD (LogicE.sound _ hD))

end
