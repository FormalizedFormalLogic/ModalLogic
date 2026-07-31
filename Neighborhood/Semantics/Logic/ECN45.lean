module

public import Neighborhood.Semantics.Logic.ECN4
public import Neighborhood.Semantics.Logic.ECN5
public import Neighborhood.Semantics.Logic.EC45
public import Neighborhood.Semantics.Logic.EN45
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_186

/-!
# The neighborhood logic `LogicECN45`

Soundness and consistency of `LogicECN45`, the classical modal logic axiomatised by the regularity
axiom `C`, `N := □⊤`, the transitivity axiom `Four` and the euclidean axiom `Five`, with respect
to the regular, unit-containing, transitive and euclidean neighborhood frames.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicECN45

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.ContainsUnit]
    [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicECN45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
theorem consistent : (@LogicECN45 α).IsConsistent := by
  by_contra! hC
  simpa using LogicECN45.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECN45 α)) :=
  MaximalConsistentSet.nonempty LogicECN45.consistent

end LogicECN45

theorem LogicECN4_ssubset_LogicECN45 : @LogicECN4 ℕ ⊂ LogicECN45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicECN4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomFive
      (LogicECN4.sound frame_2_138 hFive)

theorem LogicECN5_ssubset_LogicECN45 : @LogicECN5 ℕ ⊂ LogicECN45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicECN5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_186.not_valid_axiomFour
      (LogicECN5.sound frame_2_186 hFour)

end
