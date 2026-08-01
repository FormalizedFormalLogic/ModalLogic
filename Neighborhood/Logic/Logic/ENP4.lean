module

public import Neighborhood.Logic.Logic.ENP
public import Neighborhood.Logic.Logic.EN4
public import Neighborhood.Logic.Logic.EP4
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame2_206
public import Neighborhood.Semantics.Example.Frame3_8553090

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENP4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.NotContainsEmpty]
    [F.IsTransitive] :
    A ∈ LogicENP4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicENP4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENP4.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENP4 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicENP4.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENP4 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicENP4.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENP4 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicENP4.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicENP4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicENP4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicENP4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicENP4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicENP4 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomD (LogicENP4.sound frame_2_206 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENP4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicENP4.sound frame_2_138 (hcon #a))

end LogicENP4

end
