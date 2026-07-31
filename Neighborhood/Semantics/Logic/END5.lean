module

public import Neighborhood.Semantics.Logic.END
public import Neighborhood.Semantics.Logic.ED5
public import Neighborhood.Semantics.Logic.EN5
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame2_90

/-!
# The neighborhood logic `LogicEND5`

Soundness and consistency of `LogicEND5`, the classical modal logic axiomatised by `N := □⊤`,
the seriality axiom `D` and the euclidean axiom `Five`, with respect to the unit-containing,
serial and euclidean neighborhood frames.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicEND5

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsSerial]
    [F.IsEuclidean] :
    A ∈ LogicEND5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
theorem consistent : (@LogicEND5 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEND5.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEND5 α)) :=
  MaximalConsistentSet.nonempty LogicEND5.consistent

end LogicEND5

theorem LogicEND_ssubset_LogicEND5 : @LogicEND ℕ ⊂ LogicEND5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEND ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomFive
      (LogicEND.sound frame_2_140 hFive)

theorem LogicED5_ssubset_LogicEND5 : @LogicED5 ℕ ⊂ LogicEND5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicED5 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_90.not_valid_axiomN (LogicED5.sound frame_2_90 hN)

theorem LogicEN5_ssubset_LogicEND5 : @LogicEN5 ℕ ⊂ LogicEND5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEN5 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEN5.sound frame_1_3 hD)

end
