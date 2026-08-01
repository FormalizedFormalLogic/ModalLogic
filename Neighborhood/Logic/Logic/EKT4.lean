module

public import Neighborhood.Logic.Logic.EKT
public import Neighborhood.Logic.Logic.EK4
public import Neighborhood.Logic.Logic.ET4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_2
public import Neighborhood.Semantics.Example.Frame4_137439477800

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKT4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.IsReflexive]
    [F.IsTransitive] :
    A ∈ LogicEKT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEKT4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKT4.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEKT4 α) := by
  by_contra! hcon
  exact frame_2_2.not_valid_axiomM hab (LogicEKT4.sound frame_2_2 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEKT4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEKT4.sound frame_1_0 hcon)

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKT4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEKT4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKT4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEKT4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEKT4 α) := by
  by_contra! hcon
  exact frame_4_137439477800.not_valid_axiomC hab
    (LogicEKT4.sound frame_4_137439477800 (hcon #a #b))

end LogicEKT4

end