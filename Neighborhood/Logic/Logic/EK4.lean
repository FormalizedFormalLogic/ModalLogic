module

public import Neighborhood.Logic.Logic.EK
public import Neighborhood.Logic.Logic.E4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_90
public import Neighborhood.Semantics.Example.Frame3_6

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEK4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.IsTransitive] :
    A ∈ LogicEK4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEK4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEK4.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEK4 α) := by
  by_contra! hcon
  exact frame_2_90.not_valid_axiomM hab (LogicEK4.sound frame_2_90 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEK4 α) := by
  by_contra! hcon
  exact frame_3_6.not_valid_axiomC hab (LogicEK4.sound frame_3_6 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEK4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEK4.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEK4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEK4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEK4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEK4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEK4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEK4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEK4 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEK4.sound frame_1_3 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEK4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEK4.sound frame_1_0 (hcon #a))

end LogicEK4

end
