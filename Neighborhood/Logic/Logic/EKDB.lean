module

public import Neighborhood.Logic.Logic.EKD
public import Neighborhood.Logic.Logic.EKB
public import Neighborhood.Logic.Logic.EDB
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKDB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.IsSerial]
    [F.IsSymmetric] :
    A ∈ LogicEKDB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEKDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKDB.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEKDB α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomM hab (LogicEKDB.sound frame_1_1 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEKDB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomN (LogicEKDB.sound frame_1_1 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEKDB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEKDB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicEKDB.sound frame_1_1 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKDB α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicEKDB.sound frame_1_1 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEKDB.sound frame_2_140 (hcon #a))

end LogicEKDB

end
