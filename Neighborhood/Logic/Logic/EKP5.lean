module

public import Neighborhood.Logic.Logic.EKP
public import Neighborhood.Logic.Logic.EK5
public import Neighborhood.Logic.Logic.EP5
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_10529440

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKP5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.NotContainsEmpty]
    [F.IsEuclidean] :
    A ∈ LogicEKP5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEKP5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKP5.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEKP5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEKP5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKP5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEKP5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKP5 α) := by
  by_contra! hcon
  exact frame_3_10529440.not_valid_axiomFour (LogicEKP5.sound frame_3_10529440 (hcon #a))

end LogicEKP5

end
