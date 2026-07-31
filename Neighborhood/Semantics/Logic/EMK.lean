module

public import Neighborhood.Semantics.Logic.EK
public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_238
public import Neighborhood.Semantics.Example.Frame4_11259170869739560
public import Neighborhood.Logic.Equiv.EMK_EMCK

/-!
# The neighborhood logic `LogicEMK`

Soundness and consistency of `LogicEMK`, the classical modal logic axiomatised by the
monotonicity axiom `M` together with every instance of the axiom scheme `K`, with respect to all
monotonic neighborhood frames satisfying the `K`-property.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMK

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.HasPropertyK] :
    A ∈ LogicEMK → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp)

instance : (@LogicEMK α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMK.sound frame_1_2 hC⟩

end LogicEMK

theorem LogicEK_ssubset_LogicEMK : @LogicEK ℕ ⊂ LogicEMK := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hM : Axioms.M (#0 ⋎ #1) #1 ∈ @LogicEK ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_4_11259170869739560.not_valid_axiomM (LogicEK.sound _ hM)

theorem LogicEM_ssubset_LogicEMK : @LogicEM ℕ ⊂ LogicEMK := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hK : Axioms.K #0 #1 ∈ @LogicEM ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_238.not_valid_axiomK (LogicEM.sound _ hK)

end
