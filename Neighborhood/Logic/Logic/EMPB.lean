module

public import Neighborhood.Logic.Logic.EMB
public import Neighborhood.Logic.Logic.EMP
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMPB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.NotContainsEmpty]
    [F.IsSymmetric] :
    A ∈ LogicEMPB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMPB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMPB.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMPB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEMPB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMPB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEMPB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMPB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEMPB.sound frame_2_140 (hcon #a))

end LogicEMPB

end
