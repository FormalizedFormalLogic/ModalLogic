module

public import Neighborhood.Logic.Logic.EK4
public import Neighborhood.Logic.Logic.EK5
public import Neighborhood.Logic.Logic.E45
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_90
public import Neighborhood.Semantics.Example.Frame2_170

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEK45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.IsTransitive]
    [F.IsEuclidean] :
    A ∈ LogicEK45 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEK45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEK45.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEK45 α) := by
  by_contra! hcon
  exact frame_2_90.not_valid_axiomM hab (LogicEK45.sound frame_2_90 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEK45 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomN (LogicEK45.sound frame_2_90 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEK45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEK45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEK45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEK45.sound frame_2_170 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEK45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEK45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEK45 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEK45.sound frame_1_3 hcon)

end LogicEK45

end
