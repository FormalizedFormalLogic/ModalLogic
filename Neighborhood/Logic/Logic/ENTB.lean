module

public import Neighborhood.Logic.Logic.ETB
public import Neighborhood.Logic.Logic.ENB
public import Neighborhood.Logic.Logic.ENT
public import Neighborhood.Semantics.Example.Frame3_8437920
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_9488552

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENTB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsReflexive] [F.IsSymmetric] :
    A ∈ LogicENTB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicENTB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENTB.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENTB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicENTB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENTB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicENTB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENTB α) := by
  by_contra! hcon
  exact frame_3_9488552.not_valid_axiomC hab (LogicENTB.sound frame_3_9488552 (hcon #a #b))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENTB α) := by
  by_contra! hcon
  exact frame_3_8437920.not_valid_axiomFour (LogicENTB.sound frame_3_8437920 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENTB α) := by
  by_contra! hcon
  exact frame_3_8437920.not_valid_axiomFive (LogicENTB.sound frame_3_8437920 (hcon #a))

end LogicENTB

/-- The axiom `N` is redundant over `T` and `B`. -/
theorem LogicENTB.eq_LogicETB : (@LogicENTB α) = LogicETB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((rfl | ⟨B, rfl⟩) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomT | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

theorem LogicENTB.ssubset_LogicENT : @LogicENT ℕ ⊂ LogicENTB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicENT.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

end
