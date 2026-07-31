module

public import Neighborhood.Semantics.Logic.END
public import Neighborhood.Semantics.Logic.EDB
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame1_1

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
theorem consistent : (@LogicENDB α).IsConsistent := by
  by_contra! hC
  simpa using LogicENDB.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicENDB α)) :=
  MaximalConsistentSet.nonempty LogicENDB.consistent

end LogicENDB

theorem LogicEND_ssubset_LogicENDB : @LogicEND ℕ ⊂ LogicENDB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hB : Axioms.B #0 ∈ (@LogicEND ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomB
      (LogicEND.sound frame_2_138 hB)

theorem LogicEDB_ssubset_LogicENDB : @LogicEDB ℕ ⊂ LogicENDB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEDB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_1.not_valid_axiomN (LogicEDB.sound frame_1_1 hN)

end
