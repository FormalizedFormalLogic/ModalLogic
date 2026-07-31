module

public import Neighborhood.Semantics.Logic.EMCN4
public import Neighborhood.Semantics.Logic.EMC5
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_10529440

/-!
# The neighborhood logic `LogicEMC45`

Soundness and consistency of `LogicEMC45`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the regularity axiom `C`, the transitivity axiom `Four` and the
euclideanness axiom `Five`, with respect to the neighborhood frames that are monotonic, regular,
transitive and euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMC45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicEMC45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMC45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMC45.sound frame_1_2 hC⟩

end LogicEMC45

theorem LogicEMCN4_ssubset_LogicEMC45 : @LogicEMCN4 ℕ ⊂ LogicEMC45 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomFour
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEMCN4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomFive (LogicEMCN4.sound frame_2_138 hFive)

theorem LogicEMC5_ssubset_LogicEMC45 : @LogicEMC5 ℕ ⊂ LogicEMC45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicEMC5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_10529440.not_valid_axiomFour (LogicEMC5.sound frame_3_10529440 hFour)

end
