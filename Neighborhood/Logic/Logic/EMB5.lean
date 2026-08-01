module

public import Neighborhood.Logic.Logic.EM5
public import Neighborhood.Logic.Logic.EMB
public import Neighborhood.Semantics.Example.Frame1_3

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMB5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSymmetric]
    [F.IsEuclidean] :
    A ∈ LogicEMB5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMB5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMB5.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMB5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMB5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMB5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMB5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMB5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMB5.sound frame_1_3 hcon)

end LogicEMB5

end
