module

public import Neighborhood.Logic.Logic.EMN
public import Neighborhood.Logic.Logic.EMK
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMKN

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.HasPropertyK]
    [F.ContainsUnit] :
    A ∈ LogicEMKN → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) <;> simp)

instance : (@LogicEMKN α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMKN.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMKN α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMKN.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMKN α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEMKN.sound frame_2_138 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMKN α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMKN.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMKN α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMKN.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMKN α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEMKN.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMKN α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEMKN.sound frame_2_138 (hcon #a))

end LogicEMKN

end
