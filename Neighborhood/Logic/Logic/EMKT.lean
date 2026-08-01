module

public import Neighborhood.Logic.Logic.EMT
public import Neighborhood.Logic.Logic.EMK
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_8

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMKT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.HasPropertyK]
    [F.IsReflexive] :
    A ∈ LogicEMKT → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMKT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMKT.sound frame_1_2 hC⟩

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMKT α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMKT.sound frame_1_0 hcon)

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMKT α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMKT.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMKT α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEMKT.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMKT α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMKT.sound frame_1_0 (hcon #a))

end LogicEMKT

end
