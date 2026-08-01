module

public import Neighborhood.Logic.Logic.ENK
public import Neighborhood.Logic.Logic.EKD
public import Neighborhood.Logic.Logic.END
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_140

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENKD

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.ContainsUnit]
    [F.IsSerial] :
    A ∈ LogicENKD → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicENKD α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENKD.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicENKD α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicENKD.sound frame_2_140 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicENKD α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicENKD.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENKD α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicENKD.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENKD α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicENKD.sound frame_2_138 (hcon #a))

end LogicENKD

end
