module

public import Neighborhood.Semantics.Logic.EM4
public import Neighborhood.Semantics.Logic.ED4
public import Neighborhood.Semantics.Logic.EMD

/-!
# The neighborhood logic `LogicEMD4`

Soundness and consistency of `LogicEMD4`,
the classical modal logic axiomatised by the monotonicity axiom `M`, the seriality axiom `D` and
the transitivity axiom `Four`, with respect to the neighborhood frames that are monotonic,
transitive and serial.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMD4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsTransitive] [F.IsSerial] :
    A ∈ LogicEMD4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMD4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMD4.sound frame_1_2 hC⟩

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMD4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMD4.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMD4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEMD4.sound frame_2_170 (hcon #a))

end LogicEMD4

theorem LogicEM4_ssubset_LogicEMD4 : @LogicEM4 ℕ ⊂ LogicEMD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEM4.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicED4_ssubset_LogicEMD4 : @LogicED4 ℕ ⊂ LogicEMD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicED4.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMD_ssubset_LogicEMD4 : @LogicEMD ℕ ⊂ LogicEMD4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEMD.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

end
