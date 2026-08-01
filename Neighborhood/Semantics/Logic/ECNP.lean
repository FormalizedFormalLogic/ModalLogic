module

public import Neighborhood.Semantics.Logic.ENP
public import Neighborhood.Semantics.Logic.ECP
public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_9471106

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECNP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.ContainsUnit]
    [F.NotContainsEmpty] :
    A ∈ LogicECNP → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | rfl) <;> simp)

instance : (@LogicECNP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECNP.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECNP α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomK hab (LogicECNP.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECNP α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicECNP.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECNP α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicECNP.sound frame_2_140 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECNP α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicECNP.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECNP α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicECNP.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECNP α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicECNP.sound frame_2_138 (hcon #a))

end LogicECNP

end
