module

public import Neighborhood.Logic.Logic.EN
public import Neighborhood.Logic.Logic.EK
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENK

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.ContainsUnit] :
    A ∈ LogicENK → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, _, rfl⟩) <;> simp)

instance : (@LogicENK α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENK.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicENK α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicENK.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicENK α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicENK.sound frame_2_138 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicENK α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicENK.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicENK α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicENK.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENK α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicENK.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENK α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicENK.sound frame_2_138 (hcon #a))

end LogicENK

end
