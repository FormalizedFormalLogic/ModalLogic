module

public import Neighborhood.Logic.Logic.EDB
public import Neighborhood.Logic.Logic.ED4
public import Neighborhood.Logic.Logic.EB4
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_11570344

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEDB4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.IsSymmetric] [F.IsTransitive] :
    A ∈ LogicEDB4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEDB4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEDB4.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEDB4 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicEDB4.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEDB4 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicEDB4.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEDB4 α) := by
  by_contra! hcon
  exact frame_3_11570344.not_valid_axiomC hab (LogicEDB4.sound frame_3_11570344 (hcon #a #b))

end LogicEDB4

end
