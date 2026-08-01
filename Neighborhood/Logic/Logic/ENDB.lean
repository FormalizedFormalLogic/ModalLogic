module

public import Neighborhood.Logic.Logic.END
public import Neighborhood.Logic.Logic.EDB
public import Neighborhood.Logic.Logic.ENB
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_9488552

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENDB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsSerial]
    [F.IsSymmetric] :
    A ∈ LogicENDB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicENDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENDB.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicENDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicENDB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENDB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicENDB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENDB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicENDB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENDB α) := by
  by_contra! hcon
  exact frame_3_9488552.not_valid_axiomC hab (LogicENDB.sound frame_3_9488552 (hcon #a #b))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicENDB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicENDB.sound frame_2_140 (hcon #a))

theorem ssubset_LogicEND : @LogicEND ℕ ⊂ LogicENDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEND.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEDB : @LogicEDB ℕ ⊂ LogicENDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEDB.not_provable_axiomN⟩

theorem ssubset_LogicENB : @LogicENB ℕ ⊂ LogicENDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicENB.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicENDB

end
