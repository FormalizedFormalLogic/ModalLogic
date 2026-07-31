module

public import Neighborhood.Semantics.Logic.EK
public import Neighborhood.Semantics.Logic.EM
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
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicEK.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEM_ssubset_LogicEMK : @LogicEM ℕ ⊂ LogicEMK := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, B, hA⟩ := LogicEM.not_provable_axiomK (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.K A B, (ProvableHilbert.axm (by grind)), hA⟩

end
