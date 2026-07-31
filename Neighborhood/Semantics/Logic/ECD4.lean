module

public import Neighborhood.Semantics.Logic.ECD
public import Neighborhood.Semantics.Logic.EC4
public import Neighborhood.Semantics.Logic.ED4

/-!
# The neighborhood logic `LogicECD4`

Soundness and consistency of `LogicECD4`, the classical modal logic axiomatised by
the regularity axiom `C`, the seriality axiom `D`, and the transitivity axiom `Four`,
with respect to the neighborhood frames that are regular, serial, and transitive.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECD4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial]
    [F.IsTransitive] :
    A ∈ LogicECD4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECD4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECD4.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECD4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicECD4.sound frame_2_170 (hcon #a))

end LogicECD4

theorem LogicECD_ssubset_LogicECD4 : @LogicECD ℕ ⊂ LogicECD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicECD.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEC4_ssubset_LogicECD4 : @LogicEC4 ℕ ⊂ LogicECD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEC4.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicED4_ssubset_LogicECD4 : @LogicED4 ℕ ⊂ LogicECD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicED4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
