module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_75
public import Neighborhood.Semantics.Example.Frame3_10528928

/-!
# The neighborhood logic `LogicE5`

Soundness, consistency and completeness of `LogicE5`, the classical modal logic axiomatized by
`Five := ◇A 🡒 □◇A` over `LogicE`, with respect to the euclidean frames (`Frame.IsEuclidean`).
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicE5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsEuclidean] :
    A ∈ @LogicE5 α → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, rfl⟩; simp)

instance : (@LogicE5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicE5.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsEuclidean] → F ⊧ A) :
    A ∈ @LogicE5 α :=
  (maximalRelativeMaximalCanonicalModel LogicE5).mem_of_valid
    (h (maximalRelativeMaximalCanonicalModel LogicE5).toFrame
      (maximalRelativeMaximalCanonicalModel LogicE5).Val)

lemma not_provable_axiomC (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicE5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomC hab (LogicE5.sound frame_3_10528928 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicE5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD
    (LogicE5.sound frame_1_3 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicE5 α) := by
  by_contra! hcon
  exact frame_2_79.not_valid_axiomFour
    (LogicE5.sound frame_2_79 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicE5 α) := by
  intro hcon
  exact frame_2_75.not_valid_axiomN (LogicE5.sound frame_2_75 hcon)

omit [DecidableEq α] in
lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicE5 α) := by
  by_contra! hcon
  exact frame_1_3.not_isReflexive
    (isReflexive_of_valid_axiomT (LogicE5.sound frame_1_3 (hcon #a)))

end LogicE5

theorem LogicE_ssubset_LogicE5 : @LogicE ℕ ⊂ LogicE5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · obtain ⟨A, hA⟩ := LogicE.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

end
