module

public import Neighborhood.Semantics.Logic.ET

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

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECT α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicECT.sound frame_2_8 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECT α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicECT.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECT α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicECT.sound frame_1_0 hcon)

end LogicECT

theorem LogicET_ssubset_LogicECT : @LogicET ℕ ⊂ LogicECT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicET.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
