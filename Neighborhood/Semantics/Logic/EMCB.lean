module

public import Neighborhood.Semantics.Logic.ECB
public import Neighborhood.Semantics.Logic.EMB
public import Neighborhood.Semantics.Logic.EMC
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsSymmetric] :
    A ∈ LogicEMCB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCB.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMCB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMCB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMCB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMCB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMCB α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMCB.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMCB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEMCB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEMCB.sound frame_2_140 (hcon #a))

end LogicEMCB

end
