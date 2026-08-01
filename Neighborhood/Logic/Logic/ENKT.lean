module

public import Neighborhood.Logic.Logic.ENK
public import Neighborhood.Logic.Logic.EKT
public import Neighborhood.Logic.Logic.ENT
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_8421512

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENKT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.ContainsUnit]
    [F.IsReflexive] :
    A ∈ LogicENKT → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicENKT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENKT.sound frame_1_2 hC⟩

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicENKT α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicENKT.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENKT α) := by
  by_contra! hcon
  exact frame_3_8421512.not_valid_axiomFour (LogicENKT.sound frame_3_8421512 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENKT α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicENKT.sound frame_2_138 (hcon #a))

end LogicENKT

end
