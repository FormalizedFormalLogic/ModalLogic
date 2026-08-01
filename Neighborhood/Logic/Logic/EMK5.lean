module

public import Neighborhood.Logic.Logic.EM5
public import Neighborhood.Logic.Logic.EMK
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_10529440

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMK5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.HasPropertyK]
    [F.IsEuclidean] :
    A ∈ LogicEMK5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMK5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMK5.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMK5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMK5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMK5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEMK5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMK5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMK5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMK5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMK5.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMK5 α) := by
  by_contra! hcon
  exact frame_3_10529440.not_valid_axiomFour (LogicEMK5.sound frame_3_10529440 (hcon #a))

end LogicEMK5

end
