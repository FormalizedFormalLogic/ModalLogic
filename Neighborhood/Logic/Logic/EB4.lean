module

public import Neighborhood.Logic.Logic.EN4
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_191
public import Neighborhood.Semantics.Example.Frame3_11570344
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Logic.Logic.ENB

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEB4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSymmetric] [F.IsTransitive] :
    A ∈ LogicEB4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEB4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEB4.sound frame_1_2 hC⟩

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEB4 α) := by
  by_contra! hcon
  exact frame_3_11570344.not_valid_axiomC hab (LogicEB4.sound frame_3_11570344 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEB4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEB4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEB4 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicEB4.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEB4 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicEB4.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEB4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEB4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEB4 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEB4.sound frame_1_3 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEB4 α) := by
  by_contra! hcon
  exact frame_2_191.not_valid_axiomFive (LogicEB4.sound frame_2_191 (hcon #a))

end LogicEB4

theorem LogicEB4.ssubset_LogicENB : @LogicENB ℕ ⊂ LogicEB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (rfl | ⟨_, rfl⟩) <;> first | exact Logic.axiomN | exact Logic.axiomB
  · obtain ⟨A, hA⟩ := LogicENB.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEB4.ssubset_LogicEN4 : @LogicEN4 ℕ ⊂ LogicEB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (rfl | ⟨_, rfl⟩) <;> first | exact Logic.axiomN | exact Logic.axiomFour
  · obtain ⟨A, hA⟩ := LogicEN4.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

end
