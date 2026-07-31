module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_137520

/-!
# The neighborhood logic `LogicEC`

Soundness, consistency and completeness of `LogicEC`, the classical modal logic axiomatised by
the regularity axiom `C`, with respect to the regular neighborhood frames, and its strict
inclusion in `LogicE`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEC

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] :
    A ∈ LogicEC → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, _, rfl⟩; simp)

instance : (@LogicEC α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEC.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsRegular] → F ⊧ A) :
    A ∈ @LogicEC α :=
  (basicCanonicalModel LogicEC).mem_of_valid
    (h (basicCanonicalModel LogicEC).toFrame
      (basicCanonicalModel LogicEC).Val)

omit [DecidableEq α] in
lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEC α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEC.sound frame_1_0 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEC α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEC.sound frame_1_3 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEC α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEC.sound frame_1_0 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEC α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicEC.sound frame_1_1 (hcon #a))

lemma not_provable_axiomM (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEC α) := by
  by_contra! hcon
  exact frame_3_137520.not_valid_axiomM hab (LogicEC.sound frame_3_137520 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEC α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEC.sound frame_1_0 hcon)

end LogicEC

theorem LogicE_ssubset_LogicEC : (@LogicE ℕ) ⊂ LogicEC := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · obtain ⟨A, B, hA⟩ := LogicE.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
