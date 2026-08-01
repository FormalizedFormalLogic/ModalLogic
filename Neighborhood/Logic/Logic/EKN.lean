module

public import Neighborhood.Logic.Logic.EK
public import Neighborhood.Logic.Logic.EN
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKN

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.ContainsUnit] :
    A ∈ LogicEKN → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

instance : (@LogicEKN α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKN.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKN α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEKN.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKN α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEKN.sound frame_2_138 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEKN α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEKN.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEKN α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEKN.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKN α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEKN.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKN α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEKN.sound frame_2_138 (hcon #a))

end LogicEKN

end
