module

public import Neighborhood.Logic.Logic.EM
public import Neighborhood.Logic.Logic.EP
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame2_206
public import Neighborhood.Semantics.Example.Frame2_8

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.NotContainsEmpty] :
    A ∈ LogicEMP → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

instance : (@LogicEMP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMP.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicEMP α :=
  (supplementedBasicCanonicalModel LogicEMP).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMP).toFrame
      (supplementedBasicCanonicalModel LogicEMP).Val)

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMP α) := by
  by_contra! hcon
  exact frame_2_238.not_valid_axiomD (LogicEMP.sound frame_2_238 (hcon #a))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMP α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMP.sound frame_1_0 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMP α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicEMP.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMP α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicEMP.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMP α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEMP.sound frame_2_140 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMP.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMP α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEMP.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMP.sound frame_1_0 (hcon #a))

theorem ssubset_LogicEM : @LogicEM ℕ ⊂ LogicEMP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · exact ⟨Axioms.P, (ProvableHilbert.axm (by grind)), LogicEM.not_provable_axiomP⟩

theorem ssubset_LogicEP : @LogicEP ℕ ⊂ LogicEMP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicEP.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (Logic.HasAxiomM.M _ _), hA⟩

end LogicEMP

end
