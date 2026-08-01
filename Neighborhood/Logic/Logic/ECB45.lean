module

public import Neighborhood.Logic.Logic.EB45
public import Neighborhood.Logic.Logic.EC45
public import Neighborhood.Logic.Logic.ECB5
public import Neighborhood.Logic.Logic.ECB4
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_9472136

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECB45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSymmetric] [F.IsTransitive]
    [F.IsEuclidean] :
    A ∈ LogicECB45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECB45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECB45.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECB45 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicECB45.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECB45 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicECB45.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECB45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECB45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECB45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECB45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECB45 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicECB45.sound frame_1_3 hcon)

end LogicECB45

end
