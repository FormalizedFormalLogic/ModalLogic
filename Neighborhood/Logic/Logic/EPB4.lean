module

public import Neighborhood.Logic.Logic.EPB
public import Neighborhood.Logic.Logic.EP4
public import Neighborhood.Logic.Logic.EB4
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_11570344
public import Neighborhood.Semantics.Example.Frame3_11570364

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEPB4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.NotContainsEmpty] [F.IsSymmetric]
    [F.IsTransitive] :
    A ∈ LogicEPB4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEPB4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEPB4.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEPB4 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicEPB4.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEPB4 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicEPB4.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEPB4 α) := by
  by_contra! hcon
  exact frame_3_11570344.not_valid_axiomC hab (LogicEPB4.sound frame_3_11570344 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEPB4 α) := by
  by_contra! hcon
  exact frame_3_11570364.not_valid_axiomT (LogicEPB4.sound frame_3_11570364 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEPB4 α) := by
  by_contra! hcon
  exact frame_3_11570364.not_valid_axiomD (LogicEPB4.sound frame_3_11570364 (hcon #a))

end LogicEPB4

end
