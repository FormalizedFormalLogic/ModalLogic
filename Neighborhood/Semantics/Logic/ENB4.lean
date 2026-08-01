module

public import Neighborhood.Semantics.Logic.EB4
public import Neighborhood.Semantics.Logic.EN4
public import Neighborhood.Semantics.Logic.ENB
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_191
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_11570344

/-!
# The neighborhood logic `LogicENB4`

Soundness and consistency of `LogicENB4`, the classical modal logic axiomatised by
`N := □⊤`, the symmetry axiom `B`, and the transitivity axiom `Four`, with respect to
the neighborhood frames that contain their unit, are symmetric, and are transitive.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENB4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsSymmetric]
    [F.IsTransitive] :
    A ∈ LogicENB4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicENB4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENB4.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENB4 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicENB4.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENB4 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicENB4.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENB4 α) := by
  by_contra! hcon
  exact frame_3_11570344.not_valid_axiomC hab (LogicENB4.sound frame_3_11570344 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicENB4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicENB4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicENB4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicENB4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicENB4 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicENB4.sound frame_1_3 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENB4 α) := by
  by_contra! hcon
  exact frame_2_191.not_valid_axiomFive (LogicENB4.sound frame_2_191 (hcon #a))

end LogicENB4

end
