module

public import Neighborhood.Logic.Logic.EK
public import Neighborhood.Logic.Logic.ET
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame2_72
public import Neighborhood.Semantics.Example.Frame4_40

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.IsReflexive] :
    A ∈ LogicEKT → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEKT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKT.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEKT α) := by
  by_contra! hcon
  exact frame_2_72.not_valid_axiomM hab (LogicEKT.sound frame_2_72 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEKT α) := by
  by_contra! hcon
  exact frame_4_40.not_valid_axiomC hab (LogicEKT.sound frame_4_40 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEKT α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEKT.sound frame_1_0 hcon)

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKT α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEKT.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKT α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEKT.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKT α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEKT.sound frame_1_0 (hcon #a))

end LogicEKT

end
