module

public import Neighborhood.Semantics.Logic.ETB
public import Neighborhood.Semantics.Logic.ENB
public import Neighborhood.Semantics.Logic.ENT
public import Neighborhood.Semantics.Example.Frame3_8437920
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_9488552

/-!
# The neighborhood logic `LogicENTB`

Soundness and consistency of `LogicENTB`, the classical modal logic axiomatised by `N := □⊤`,
the reflexivity axiom `T` and the symmetry axiom `B`, with respect to the neighborhood frames
that contain their unit, are reflexive and are symmetric.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicENTB

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsReflexive] [F.IsSymmetric] :
    A ∈ LogicENTB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicENTB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENTB.sound frame_1_2 hC⟩

lemma not_provable_axiomK (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENTB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicENTB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENTB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicENTB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomC (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENTB α) := by
  by_contra! hcon
  exact frame_3_9488552.not_valid_axiomC hab (LogicENTB.sound frame_3_9488552 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENTB α) := by
  by_contra! hcon
  exact frame_3_8437920.not_valid_axiomFour (LogicENTB.sound frame_3_8437920 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENTB α) := by
  by_contra! hcon
  exact frame_3_8437920.not_valid_axiomFive (LogicENTB.sound frame_3_8437920 (hcon #a))

end LogicENTB

end
