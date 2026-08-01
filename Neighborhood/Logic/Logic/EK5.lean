module

public import Neighborhood.Logic.Logic.EK
public import Neighborhood.Logic.Logic.E5
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_79
public import Neighborhood.Semantics.Example.Frame2_90
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_1245183

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEK5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.IsEuclidean] :
    A ∈ LogicEK5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEK5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEK5.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEK5 α) := by
  by_contra! hcon
  exact frame_2_79.not_valid_axiomM hab (LogicEK5.sound frame_2_79 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEK5 α) := by
  by_contra! hcon
  exact frame_3_1245183.not_valid_axiomC hab (LogicEK5.sound frame_3_1245183 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEK5 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomN (LogicEK5.sound frame_2_90 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEK5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEK5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEK5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEK5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEK5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEK5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEK5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEK5.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEK5 α) := by
  by_contra! hcon
  exact frame_2_79.not_valid_axiomFour (LogicEK5.sound frame_2_79 (hcon #a))

end LogicEK5

end
