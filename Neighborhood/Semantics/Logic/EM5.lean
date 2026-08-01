module

public import Neighborhood.Semantics.Logic.EN5
public import Neighborhood.Semantics.Logic.EMN
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame2_206

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEM5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsEuclidean] :
    A ∈ LogicEM5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEM5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEM5.sound frame_1_2 hC⟩

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEM5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomC hab (LogicEM5.sound frame_3_10528928 (hcon #a #b))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEM5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEM5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEM5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomFour (LogicEM5.sound frame_3_10528928 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEM5 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicEM5.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEM5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEM5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEM5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEM5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEM5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEM5.sound frame_1_3 hcon)

end LogicEM5

theorem LogicEN5_ssubset_LogicEM5 : @LogicEN5 ℕ ⊂ LogicEM5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (rfl | ⟨_, rfl⟩) <;> first | exact Logic.axiomN | exact Logic.axiomFive
  · obtain ⟨A, B, hA⟩ := LogicEN5.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMN_ssubset_LogicEM5 : @LogicEMN ℕ ⊂ LogicEM5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (⟨_, _, rfl⟩ | rfl) <;> first | exact Logic.axiomM | exact Logic.axiomN
  · obtain ⟨A, hA⟩ := LogicEMN.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

end
