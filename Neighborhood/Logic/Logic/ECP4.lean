module

public import Neighborhood.Logic.Logic.ECP
public import Neighborhood.Logic.Logic.EC4
public import Neighborhood.Logic.Logic.EP4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_8553090

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECP4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.NotContainsEmpty]
    [F.IsTransitive] :
    A ∈ LogicECP4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECP4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECP4.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECP4 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomK hab (LogicECP4.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECP4 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicECP4.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECP4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicECP4.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECP4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicECP4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECP4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicECP4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECP4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicECP4.sound frame_1_0 (hcon #a))

end LogicECP4

end
