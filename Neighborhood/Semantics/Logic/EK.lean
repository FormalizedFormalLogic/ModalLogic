module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Example.Frame4_11259170869739560

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

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEK α) := by
  by_contra! hcon
  exact frame_4_11259170869739560.not_valid_axiomM hab (LogicEK.sound _ (hcon (#a ⋎ #b) #b))

end LogicEK

theorem LogicE_ssubset_LogicEK : @LogicE ℕ ⊂ LogicEK := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · obtain ⟨A, B, hA⟩ := LogicE.not_provable_axiomK (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.K A B, (ProvableHilbert.axm (by grind)), hA⟩

end
