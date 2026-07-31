module

public import Neighborhood.Semantics.Logic.ET
public import Neighborhood.Semantics.Logic.EMD
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame3_168

/-!
# The neighborhood logic `LogicEMT`

Soundness, consistency and completeness of `LogicEMT`, the classical modal logic axiomatised by
the monotonicity axiom `M` and the reflexivity axiom `T`, with respect to the neighborhood frames
that are both monotonic and reflexive.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsReflexive] :
    A ∈ LogicEMT → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMT.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsReflexive] → F ⊧ A) :
    A ∈ @LogicEMT α :=
  (supplementedBasicCanonicalModel LogicEMT).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMT).toFrame
      (supplementedBasicCanonicalModel LogicEMT).Val)

lemma not_provable_axiomC (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMT α) := by
  by_contra! hcon
  exact frame_3_168.not_valid_axiomC hab (LogicEMT.sound frame_3_168 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMT α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour
    (LogicEMT.sound frame_2_8 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMT α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMT.sound frame_1_0 hcon)

lemma not_provable_axiomK (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMT α) := by
  by_contra! hcon
  exact frame_3_168.not_valid_axiomK hab (LogicEMT.sound frame_3_168 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMT α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMT.sound frame_1_0 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMT α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMT.sound frame_1_0 (hcon #a))

end LogicEMT

theorem LogicET_ssubset_LogicEMT : @LogicET ℕ ⊂ LogicEMT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicET.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMD_ssubset_LogicEMT : @LogicEMD ℕ ⊂ LogicEMT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩)
    · exact ProvableHilbert.axm (by grind)
    · exact Logic.axiomD
  · obtain ⟨A, hA⟩ := LogicEMD.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end
