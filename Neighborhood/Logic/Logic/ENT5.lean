module

public import Neighborhood.Logic.Logic.ET5
public import Neighborhood.Logic.Logic.EN5
public import Neighborhood.Logic.Logic.ENT
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

/-- The axiom `N` is redundant over `T` and `5`. -/
theorem LogicENT5.eq_LogicET5 : (@LogicENT5 α) = LogicET5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomFive
  · exact Hilbert.subset_of_subset_axioms (by grind)

end
