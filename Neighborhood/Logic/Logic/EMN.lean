module

public import Neighborhood.Logic.Logic.EM
public import Neighborhood.Logic.Logic.EN
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_206

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMN

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.ContainsUnit] :
    A ∈ LogicEMN → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

instance : (@LogicEMN α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMN.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] → F ⊧ A) :
    A ∈ @LogicEMN α :=
  (supplementedBasicCanonicalModel LogicEMN).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMN).toFrame
      (supplementedBasicCanonicalModel LogicEMN).Val)

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMN α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab
    (LogicEMN.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMN α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEMN.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMN α) := by
  by_contra! hcon
  exact frame_2_172.not_valid_axiomFour (LogicEMN.sound frame_2_172 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMN α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMN.sound frame_1_3 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMN α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicEMN.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMN α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMN.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMN α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEMN.sound frame_2_138 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMN α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMN.sound frame_1_3 (hcon #a))

theorem ssubset_LogicEM : @LogicEM ℕ ⊂ LogicEMN := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEM.not_provable_axiomN⟩

theorem ssubset_LogicEN : @LogicEN ℕ ⊂ LogicEMN := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicEN.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMN

end
