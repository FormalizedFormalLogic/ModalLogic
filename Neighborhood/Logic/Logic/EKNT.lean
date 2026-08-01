module

public import Neighborhood.Logic.Logic.EKN
public import Neighborhood.Logic.Logic.EKT
public import Neighborhood.Logic.Logic.ENT
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_8421512

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEKNT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] [F.ContainsUnit]
    [F.IsReflexive] :
    A ∈ LogicEKNT → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEKNT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEKNT.sound frame_1_2 hC⟩

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEKNT α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEKNT.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEKNT α) := by
  by_contra! hcon
  exact frame_3_8421512.not_valid_axiomFour (LogicEKNT.sound frame_3_8421512 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEKNT α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEKNT.sound frame_2_138 (hcon #a))

end LogicEKNT

end
