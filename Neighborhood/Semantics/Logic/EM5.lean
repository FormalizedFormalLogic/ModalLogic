module

public import Neighborhood.Semantics.Logic.EN5
public import Neighborhood.Semantics.Logic.EMN
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_153
public import Neighborhood.Semantics.Example.Frame2_140

/-!
# The neighborhood logic `LogicEM5`

Soundness and consistency of `LogicEM5`, the classical modal logic axiomatised by the
monotonicity axiom `M` and the euclideanness axiom `Five`, with respect to the neighborhood
frames that are monotonic and euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEM5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsEuclidean] :
    A ∈ LogicEM5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEM5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEM5.sound frame_1_2 hC⟩

end LogicEM5

theorem LogicEN5_ssubset_LogicEM5 : @LogicEN5 ℕ ⊂ LogicEM5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (rfl | ⟨_, rfl⟩) <;> first | exact Logic.axiomN | exact Logic.axiomFive
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicEN5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_153.not_valid_axiomM (LogicEN5.sound frame_2_153 hM)

theorem LogicEMN_ssubset_LogicEM5 : @LogicEMN ℕ ⊂ LogicEM5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (⟨_, _, rfl⟩ | rfl) <;> first | exact Logic.axiomM | exact Logic.axiomN
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEMN ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomFive (LogicEMN.sound frame_2_140 hFive)

end
