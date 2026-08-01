module

public import Neighborhood.Semantics.Logic.EMP
public import Neighborhood.Semantics.Logic.EMK
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMKP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.HasPropertyK]
    [F.NotContainsEmpty] :
    A ∈ LogicEMKP → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) <;> simp)

instance : (@LogicEMKP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMKP.sound frame_1_2 hC⟩

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMKP α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMKP.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMKP α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEMKP.sound frame_2_140 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMKP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMKP.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMKP α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEMKP.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMKP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMKP.sound frame_1_0 (hcon #a))

end LogicEMKP

end
