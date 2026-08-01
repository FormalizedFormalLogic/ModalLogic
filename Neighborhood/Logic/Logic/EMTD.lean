module

public import Neighborhood.Logic.Logic.EMD
public import Neighborhood.Logic.Logic.EMT
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame3_8421544

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMTD

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsReflexive]
    [F.IsSerial] :
    A ∈ LogicEMTD → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMTD α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMTD.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMTD α) := by
  by_contra! hcon
  exact frame_3_8421544.not_valid_axiomK hab (LogicEMTD.sound frame_3_8421544 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMTD α) := by
  by_contra! hcon
  exact frame_3_8421544.not_valid_axiomC hab (LogicEMTD.sound frame_3_8421544 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMTD α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMTD.sound frame_1_0 hcon)

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMTD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMTD.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMTD α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEMTD.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMTD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMTD.sound frame_1_0 (hcon #a))

end LogicEMTD

end
