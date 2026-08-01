module

public import Neighborhood.Logic.Logic.EKB
public import Neighborhood.Logic.Logic.EK5
public import Neighborhood.Logic.Logic.EB5
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_79

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKB5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.IsSymmetric]
    [F.IsEuclidean] :
    A ∈ LogicEKB5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEKB5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKB5.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEKB5 α) := by
  by_contra! hcon
  exact frame_2_79.not_valid_axiomM hab (LogicEKB5.sound frame_2_79 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEKB5 α) := by
  intro hcon
  exact frame_2_79.not_valid_axiomN (LogicEKB5.sound frame_2_79 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKB5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEKB5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEKB5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEKB5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEKB5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEKB5.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKB5 α) := by
  by_contra! hcon
  exact frame_2_79.not_valid_axiomFour (LogicEKB5.sound frame_2_79 (hcon #a))

end LogicEKB5

end
