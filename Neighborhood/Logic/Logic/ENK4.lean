module

public import Neighborhood.Logic.Logic.ENK
public import Neighborhood.Logic.Logic.EK4
public import Neighborhood.Logic.Logic.EN4
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_138

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENK4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.ContainsUnit]
    [F.IsTransitive] :
    A ∈ LogicENK4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicENK4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENK4.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicENK4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicENK4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicENK4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicENK4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicENK4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicENK4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicENK4 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicENK4.sound frame_1_3 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENK4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicENK4.sound frame_2_138 (hcon #a))

end LogicENK4

end
