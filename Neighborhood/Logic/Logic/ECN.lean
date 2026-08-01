module

public import Neighborhood.Logic.Logic.EC
public import Neighborhood.Logic.Logic.EN
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_137
public import Neighborhood.Semantics.Example.Frame2_153

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECN

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] :
    A ∈ LogicECN → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

instance : (@LogicECN α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECN.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsRegular] → [F.ContainsUnit] → F ⊧ A) :
    A ∈ @LogicECN α :=
  (basicCanonicalModel LogicECN).mem_of_valid
    (h (basicCanonicalModel LogicECN).toFrame
      (basicCanonicalModel LogicECN).Val)

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECN α) := by
  by_contra! hcon
  exact frame_2_137.not_valid_axiomB
    (LogicECN.sound frame_2_137 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECN α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECN.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECN α) := by
  by_contra! hcon
  exact frame_2_137.not_valid_axiomFive
    (LogicECN.sound frame_2_137 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECN α) := by
  by_contra! hcon
  exact frame_2_137.not_valid_axiomFour
    (LogicECN.sound frame_2_137 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECN α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomM hab
    (LogicECN.sound frame_2_153 (hcon #a #b))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECN α) := by
  by_contra! hcon
  exact frame_2_137.not_valid_axiomK hab (LogicECN.sound frame_2_137 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECN α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECN.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECN α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicECN.sound frame_1_3 hcon)

theorem ssubset_LogicEC : @LogicEC ℕ ⊂ LogicECN := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEC.not_provable_axiomN⟩

theorem ssubset_LogicEN : @LogicEN ℕ ⊂ LogicECN := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicEN.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicECN

end
