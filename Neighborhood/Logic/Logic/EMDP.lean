module

public import Neighborhood.Logic.Logic.EMP
public import Neighborhood.Logic.Logic.EMD
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_43176

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMDP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSerial]
    [F.NotContainsEmpty] :
    A ∈ LogicEMDP → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | rfl) <;> simp)

instance : (@LogicEMDP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMDP.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMDP α) := by
  by_contra! hcon
  exact frame_3_43176.not_valid_axiomK hab (LogicEMDP.sound frame_3_43176 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMDP α) := by
  by_contra! hcon
  exact frame_3_43176.not_valid_axiomC hab (LogicEMDP.sound frame_3_43176 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMDP α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMDP.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMDP α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEMDP.sound frame_2_140 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMDP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMDP.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMDP α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEMDP.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMDP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMDP.sound frame_1_0 (hcon #a))

end LogicEMDP

end
