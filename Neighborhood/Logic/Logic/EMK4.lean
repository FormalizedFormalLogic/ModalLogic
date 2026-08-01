module

public import Neighborhood.Logic.Logic.EM4
public import Neighborhood.Logic.Logic.EMK
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMK4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.HasPropertyK]
    [F.IsTransitive] :
    A ∈ LogicEMK4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMK4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMK4.sound frame_1_2 hC⟩

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMK4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMK4.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMK4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMK4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMK4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMK4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMK4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMK4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMK4 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMK4.sound frame_1_3 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMK4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMK4.sound frame_1_0 (hcon #a))

end LogicEMK4

end
