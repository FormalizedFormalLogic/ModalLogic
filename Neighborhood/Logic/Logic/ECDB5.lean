module

public import Neighborhood.Logic.Logic.EDB5
public import Neighborhood.Logic.Logic.ECB5
public import Neighborhood.Logic.Logic.ECD5
public import Neighborhood.Logic.Logic.ECDB
public import Neighborhood.Semantics.Example.Frame3_9472136

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECDB5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial] [F.IsSymmetric]
    [F.IsEuclidean] :
    A ∈ LogicECDB5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECDB5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECDB5.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECDB5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicECDB5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECDB5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicECDB5.sound frame_3_9472136 (hcon #a #b))

end LogicECDB5

end
