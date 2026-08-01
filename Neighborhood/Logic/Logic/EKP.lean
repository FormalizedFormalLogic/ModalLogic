module

public import Neighborhood.Logic.Logic.EK
public import Neighborhood.Logic.Logic.EP
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame2_34
public import Neighborhood.Semantics.Example.Frame4_11259170869739560

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.NotContainsEmpty] :
    A ∈ LogicEKP → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

instance : (@LogicEKP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKP.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEKP α) := by
  by_contra! hcon
  exact frame_2_34.not_valid_axiomM hab (LogicEKP.sound frame_2_34 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEKP α) := by
  by_contra! hcon
  exact frame_4_11259170869739560.not_valid_axiomC hab (LogicEKP.sound frame_4_11259170869739560 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEKP α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEKP.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKP α) := by
  by_contra! hcon
  exact frame_2_34.not_valid_axiomT (LogicEKP.sound frame_2_34 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEKP.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKP α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEKP.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEKP.sound frame_1_0 (hcon #a))

end LogicEKP

end
