module

public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame3_130

/-!
# The neighborhood logic `LogicEK`

Soundness and consistency of `LogicEK`, obtained from `LogicE` by adding every instance of the
axiom scheme `K`, with respect to all neighborhood frames satisfying the `K`-property.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEK

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] :
    A ∈ LogicEK → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, _, rfl⟩; simp)

instance : (@LogicEK α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEK.sound frame_1_2 hC⟩

end LogicEK

theorem LogicE_ssubset_LogicEK : @LogicE ℕ ⊂ LogicEK := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hK : Axioms.K #0 #1 ∈ @LogicE ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_130.not_valid_axiomK (LogicE.sound _ hK)

end
