module

public import Neighborhood.Semantics.Logic.END
public import Neighborhood.Semantics.Logic.EDB
public import Neighborhood.Semantics.Logic.ENB

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
lemma not_provable_axiomT {a : α} : ∃ A, Axioms.T A ∉ (@LogicENDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicENDB.sound frame_2_140 (hcon #a))

end LogicENDB

theorem LogicEND_ssubset_LogicENDB : @LogicEND ℕ ⊂ LogicENDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEND.not_provable_axiomB (a := (0 : ℕ))
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
  · obtain ⟨A, hA⟩ := LogicENB.not_provable_axiomD (a := (0 : ℕ))
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
