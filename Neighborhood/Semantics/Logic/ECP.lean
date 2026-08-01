module

public import Neighborhood.Semantics.Logic.EP
public import Neighborhood.Semantics.Logic.ECD
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_34
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame3_9471106

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.NotContainsEmpty] :
    A ∈ LogicECP → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

instance : (@LogicECP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECP.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsRegular] → [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicECP α :=
  (basicCanonicalModel LogicECP).mem_of_valid
    (h (basicCanonicalModel LogicECP).toFrame
      (basicCanonicalModel LogicECP).Val)

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECP α) := by
  by_contra! hcon
  exact frame_2_34.not_valid_axiomM hab (LogicECP.sound frame_2_34 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECP α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicECP.sound frame_1_0 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECP α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomK hab (LogicECP.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECP α) := by
  by_contra! hcon
  exact frame_2_34.not_valid_axiomT (LogicECP.sound frame_2_34 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicECP.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECP α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicECP.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicECP.sound frame_1_0 (hcon #a))

end LogicECP

theorem LogicECD_ssubset_LogicECP : @LogicECD ℕ ⊂ LogicECP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, C, rfl⟩ | ⟨B, rfl⟩) <;> first | exact Logic.axiomC | exact Logic.axiomD
  · exact ⟨Axioms.P, (ProvableHilbert.axm (by grind)), LogicECD.not_provable_axiomP⟩

theorem LogicEP_ssubset_LogicECP : @LogicEP ℕ ⊂ LogicECP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicEP.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (Logic.HasAxiomC.C _ _), hA⟩

end
