module

public import Neighborhood.Semantics.Logic.EM5
public import Neighborhood.Semantics.Logic.EMP
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame2_206
public import Neighborhood.Semantics.Example.Frame3_10528928

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMP5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.NotContainsEmpty]
    [F.IsEuclidean] :
    A ∈ LogicEMP5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMP5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMP5.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMP5 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicEMP5.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMP5 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicEMP5.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMP5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEMP5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMP5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEMP5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMP5 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomD (LogicEMP5.sound frame_2_206 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMP5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomFour (LogicEMP5.sound frame_3_10528928 (hcon #a))

end LogicEMP5

end
