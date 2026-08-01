module

public import Neighborhood.Semantics.Logic.EMP
public import Neighborhood.Semantics.Logic.EMT
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame3_168

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMTP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsReflexive]
    [F.NotContainsEmpty] :
    A ∈ LogicEMTP → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | rfl) <;> simp)

instance : (@LogicEMTP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMTP.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMTP α) := by
  by_contra! hcon
  exact frame_3_168.not_valid_axiomK hab (LogicEMTP.sound frame_3_168 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMTP α) := by
  by_contra! hcon
  exact frame_3_168.not_valid_axiomC hab (LogicEMTP.sound frame_3_168 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMTP α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMTP.sound frame_1_0 hcon)

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMTP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMTP.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMTP α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEMTP.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMTP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMTP.sound frame_1_0 (hcon #a))

end LogicEMTP

end
