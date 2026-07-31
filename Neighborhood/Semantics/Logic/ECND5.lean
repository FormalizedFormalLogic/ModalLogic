module

public import Neighborhood.Semantics.Logic.ECND
public import Neighborhood.Semantics.Logic.ECN5
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_140

/-!
# The neighborhood logic `LogicECND5`

Soundness and consistency of `LogicECND5`, the classical modal logic axiomatised by
the regularity axiom `C`, `N := □⊤`, the seriality axiom `D` and the Euclidean axiom `Five`
over `LogicE`, with respect to the regular, unit-containing, serial and Euclidean neighborhood frames.
Also proves the strict inclusions of `LogicECND` and `LogicECN5` in `LogicECND5`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicECND5.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] [F.IsSerial] [F.IsEuclidean] :
    A ∈ LogicECND5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicECND5.consistent : (@LogicECND5 α).IsConsistent := by
  by_contra! hC
  simpa using LogicECND5.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECND5 α)) :=
  MaximalConsistentSet.nonempty LogicECND5.consistent

theorem LogicECND_ssubset_LogicECND5 : @LogicECND ℕ ⊂ LogicECND5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFive : Axioms.Five #0 ∈ @LogicECND ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomFive (LogicECND.sound frame_2_140 hFive)

theorem LogicECN5_ssubset_LogicECND5 : @LogicECN5 ℕ ⊂ LogicECND5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ @LogicECN5 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicECN5.sound frame_1_3 hD)

end
