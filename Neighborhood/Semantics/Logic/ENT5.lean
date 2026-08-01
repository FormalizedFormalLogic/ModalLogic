module

public import Neighborhood.Semantics.Logic.ET5
public import Neighborhood.Semantics.Logic.EN5
public import Neighborhood.Semantics.Logic.ENT
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_11570344

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENT5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsReflexive] [F.IsEuclidean] :
    A ∈ LogicENT5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicENT5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENT5.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENT5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicENT5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENT5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicENT5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENT5 α) := by
  by_contra! hcon
  exact frame_3_11570344.not_valid_axiomC hab (LogicENT5.sound frame_3_11570344 (hcon #a #b))

end LogicENT5

end
