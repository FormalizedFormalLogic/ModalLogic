module

public import Neighborhood.Logic.Logic.EN45
public import Neighborhood.Logic.Logic.EM5
public import Neighborhood.Logic.Logic.EMN4
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame2_206

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEM45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicEM45 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEM45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEM45.sound frame_1_2 hC⟩

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEM45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEM45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEM45 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicEM45.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEM45 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicEM45.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEM45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEM45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEM45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEM45.sound frame_2_170 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEM45 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEM45.sound frame_1_3 hcon)

theorem ssubset_LogicEN45 : @LogicEN45 ℕ ⊂ LogicEM45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEN45.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMN4 : @LogicEMN4 ℕ ⊂ LogicEM45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMN4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEM5 : @LogicEM5 ℕ ⊂ LogicEM45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEM5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEM45

end
