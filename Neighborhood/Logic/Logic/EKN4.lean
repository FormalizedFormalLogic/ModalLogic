module

public import Neighborhood.Logic.Logic.EKN
public import Neighborhood.Logic.Logic.EK4
public import Neighborhood.Logic.Logic.EN4
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_138

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKN4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.ContainsUnit]
    [F.IsTransitive] :
    A ∈ LogicEKN4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEKN4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKN4.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKN4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEKN4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKN4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEKN4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEKN4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEKN4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEKN4 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEKN4.sound frame_1_3 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKN4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEKN4.sound frame_2_138 (hcon #a))

end LogicEKN4

end
