module

public import Neighborhood.Semantics.Logic.EN4
public import Neighborhood.Semantics.Logic.EN5
public import Neighborhood.Semantics.Logic.E45
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_186
public import Neighborhood.Semantics.Example.Frame2_75

/-!
# The neighborhood logic `LogicEN45`

Soundness and consistency of `LogicEN45`, the classical modal logic axiomatised by `N := □⊤`,
the transitivity axiom `Four` and the euclidean axiom `Five`, with respect to the unit-containing,
transitive and euclidean neighborhood frames.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicEN45

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicEN45 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
theorem consistent : (@LogicEN45 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEN45.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEN45 α)) :=
  MaximalConsistentSet.nonempty LogicEN45.consistent

end LogicEN45

theorem LogicEN4_ssubset_LogicEN45 : @LogicEN4 ℕ ⊂ LogicEN45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEN4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomFive
      (LogicEN4.sound frame_2_138 hFive)

theorem LogicEN5_ssubset_LogicEN45 : @LogicEN5 ℕ ⊂ LogicEN45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicEN5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_186.not_valid_axiomFour
      (LogicEN5.sound frame_2_186 hFour)

theorem LogicE45_ssubset_LogicEN45 : @LogicE45 ℕ ⊂ LogicEN45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicE45 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_75.not_valid_axiomN (LogicE45.sound frame_2_75 hN)

end
