module

public import Neighborhood.Semantics.Logic.EMB
public import Neighborhood.Semantics.Logic.EMK
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMKB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.HasPropertyK]
    [F.IsSymmetric] :
    A ∈ LogicEMKB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMKB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMKB.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMKB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMKB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMKB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMKB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMKB α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMKB.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMKB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEMKB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMKB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEMKB.sound frame_2_140 (hcon #a))

end LogicEMKB

end
