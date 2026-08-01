module

public import Neighborhood.Logic.Logic.END4
public import Neighborhood.Logic.Logic.EN45
public import Neighborhood.Logic.Logic.ED45
public import Neighborhood.Semantics.Example.Frame3_8553090
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_11570344

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEND45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsSerial]
    [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicEND45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEND45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEND45.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEND45 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicEND45.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEND45 α) := by
  by_contra! hcon
  exact frame_3_11570344.not_valid_axiomC hab (LogicEND45.sound frame_3_11570344 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEND45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEND45.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEND45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEND45.sound frame_2_170 (hcon #a))

theorem ssubset_LogicEND4 : @LogicEND4 ℕ ⊂ LogicEND45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEND4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEND45

end
