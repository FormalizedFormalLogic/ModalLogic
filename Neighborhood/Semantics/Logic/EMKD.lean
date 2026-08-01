module

public import Neighborhood.Semantics.Logic.EMD
public import Neighborhood.Semantics.Logic.EMK
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMKD

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.HasPropertyK]
    [F.IsSerial] :
    A ∈ LogicEMKD → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMKD α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMKD.sound frame_1_2 hC⟩

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMKD α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMKD.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMKD α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEMKD.sound frame_2_140 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMKD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMKD.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMKD α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEMKD.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMKD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMKD.sound frame_1_0 (hcon #a))

end LogicEMKD

end
