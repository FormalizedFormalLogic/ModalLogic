module

public import Neighborhood.Semantics.Logic.END
public import Neighborhood.Semantics.Logic.EDB
public import Neighborhood.Semantics.Logic.ENB
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_9488552

/-!
# The neighborhood logic `LogicENDB`

Soundness and consistency of `LogicENDB`, the classical modal logic axiomatised by `N := □⊤`,
the seriality axiom `D` and the symmetry axiom `B`, with respect to the unit-containing, serial
and symmetric neighborhood frames.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicENDB

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsSerial]
    [F.IsSymmetric] :
    A ∈ LogicENDB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicENDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENDB.sound frame_1_2 hC⟩

omit [DecidableEq α] in
lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicENDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicENDB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomK (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENDB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicENDB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENDB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicENDB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomC (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENDB α) := by
  by_contra! hcon
  exact frame_3_9488552.not_valid_axiomC hab (LogicENDB.sound frame_3_9488552 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicENDB.sound frame_2_140 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicENDB.sound frame_2_140 (hcon #a))

end LogicENDB

theorem LogicEND_ssubset_LogicENDB : @LogicEND ℕ ⊂ LogicENDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEND.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEDB_ssubset_LogicENDB : @LogicEDB ℕ ⊂ LogicENDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEDB.not_provable_axiomN⟩

theorem LogicENB_ssubset_LogicENDB : @LogicENB ℕ ⊂ LogicENDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicENB.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
