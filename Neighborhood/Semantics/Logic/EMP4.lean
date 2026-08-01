module

public import Neighborhood.Semantics.Logic.EM4
public import Neighborhood.Semantics.Logic.EMP
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame2_206

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMP4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.NotContainsEmpty]
    [F.IsTransitive] :
    A ∈ LogicEMP4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMP4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMP4.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMP4 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicEMP4.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMP4 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicEMP4.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMP4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMP4.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMP4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEMP4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMP4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMP4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMP4 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomD (LogicEMP4.sound frame_2_206 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMP4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMP4.sound frame_1_0 (hcon #a))

end LogicEMP4

end
