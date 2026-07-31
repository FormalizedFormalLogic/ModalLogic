module

public import Neighborhood.Semantics.Logic.ED4
public import Neighborhood.Semantics.Logic.E45
public import Neighborhood.Semantics.Logic.ED5
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_10528928

/-!
# The neighborhood logic `LogicED45`

Soundness and consistency of `LogicED45`, the classical modal logic axiomatised by the seriality
axiom `D`, the transitivity axiom `4`, and the euclideanity axiom `5`, with respect to the serial,
transitive, and euclidean neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicED45.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.IsTransitive]
    [F.IsEuclidean] :
    A ∈ LogicED45 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicED45.consistent : (@LogicED45 α).IsConsistent := by
  by_contra! hC
  simpa using LogicED45.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicED45 α)) :=
  MaximalConsistentSet.nonempty LogicED45.consistent

theorem LogicED4_ssubset_LogicED45 : @LogicED4 ℕ ⊂ LogicED45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFive : Axioms.Five #0 ∈ @LogicED4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomFive (LogicED4.sound frame_1_0 hFive)

theorem LogicE45_ssubset_LogicED45 : @LogicE45 ℕ ⊂ LogicED45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ @LogicE45 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicE45.sound frame_1_3 hD)

theorem LogicED5_ssubset_LogicED45 : @LogicED5 ℕ ⊂ LogicED45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFour : Axioms.Four #0 ∈ @LogicED5 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_10528928.not_valid_axiomFour (LogicED5.sound frame_3_10528928 hFour)

end
