module

public import Neighborhood.Logic.Logic.EKN
public import Neighborhood.Logic.Logic.EKD
public import Neighborhood.Logic.Logic.END
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKND

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.ContainsUnit]
    [F.IsSerial] :
    A ∈ LogicEKND → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEKND α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKND.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEKND.sound frame_2_140 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKND α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEKND.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEKND.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKND α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEKND.sound frame_2_138 (hcon #a))

end LogicEKND

end
