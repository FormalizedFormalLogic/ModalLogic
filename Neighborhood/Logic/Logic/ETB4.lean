module

public import Neighborhood.Logic.Logic.ETB
public import Neighborhood.Logic.Logic.ET4
public import Neighborhood.Logic.Logic.EB4
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_11570344

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicETB4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsReflexive] [F.IsSymmetric] [F.IsTransitive] :
    A ∈ LogicETB4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicETB4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicETB4.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicETB4 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicETB4.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicETB4 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicETB4.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicETB4 α) := by
  by_contra! hcon
  exact frame_3_11570344.not_valid_axiomC hab (LogicETB4.sound frame_3_11570344 (hcon #a #b))

end LogicETB4

end
