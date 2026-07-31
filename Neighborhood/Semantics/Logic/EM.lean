module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Supplementation
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_206
public import Neighborhood.Semantics.Example.Frame2_238

/-!
# The neighborhood logic `LogicEM`

Soundness, consistency and completeness of `LogicEM`, the classical modal logic axiomatised by
the monotonicity axiom `M`, with respect to all monotonic neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEM

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] :
    A ∈ LogicEM → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, _, rfl⟩; simp)

instance : (@LogicEM α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEM.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → F ⊧ A) :
    A ∈ @LogicEM α :=
  (supplementedBasicCanonicalModel LogicEM).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEM).toFrame
      (supplementedBasicCanonicalModel LogicEM).Val)

omit [DecidableEq α] in
lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEM α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEM.sound frame_2_8 (hcon #a))

lemma not_provable_axiomK (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEM α) := by
  by_contra! hcon
  exact frame_2_238.not_valid_axiomK hab (LogicEM.sound _ (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEM α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEM.sound frame_1_0 hcon)

omit [DecidableEq α] in
lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEM α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEM.sound frame_1_3 hcon)

lemma not_provable_axiomC (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEM α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicEM.sound _ (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEM α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEM.sound frame_1_3 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEM α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEM.sound frame_1_0 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEM α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEM.sound frame_1_3 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEM α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEM.sound frame_1_0 (hcon #a))

end LogicEM

theorem LogicE_ssubset_LogicEM : @LogicE ℕ ⊂ LogicEM := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · obtain ⟨A, B, hA⟩ := LogicE.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
