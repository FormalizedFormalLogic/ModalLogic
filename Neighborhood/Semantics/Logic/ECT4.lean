module

public import Neighborhood.Semantics.Logic.ET4
public import Neighborhood.Semantics.Logic.ECT
public import Neighborhood.Semantics.Logic.ECD4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame3_9471106

/-!
# The neighborhood logic `LogicECT4`

Soundness and consistency of `LogicECT4`, the classical modal logic axiomatised by the regularity
axiom `C`, the reflexivity axiom `T`, and the transitivity axiom `Four`, with respect to the
regular, reflexive, and transitive neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECT4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsReflexive]
    [F.IsTransitive] :
    A ∈ LogicECT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECT4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECT4.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECT4 α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomK hab (LogicECT4.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECT4 α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicECT4.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECT4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicECT4.sound frame_1_0 hcon)

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECT4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicECT4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECT4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicECT4.sound frame_1_0 (hcon #a))

end LogicECT4

theorem LogicET4_ssubset_LogicECT4 : @LogicET4 ℕ ⊂ LogicECT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicET4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECT_ssubset_LogicECT4 : @LogicECT ℕ ⊂ LogicECT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECT.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECD4_ssubset_LogicECT4 : @LogicECD4 ℕ ⊂ LogicECT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩)
    · exact ProvableHilbert.axm (by grind)
    · exact Logic.axiomD
    · exact ProvableHilbert.axm (by grind)
  · obtain ⟨A, hA⟩ := LogicECD4.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end
