module

public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.E5
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3

/-!
# The neighborhood logic `LogicED5`

Soundness and consistency of `LogicED5`, the classical modal logic axiomatised by
the seriality axiom `D` and the Euclideanity axiom `Five`, with respect to
the serial and Euclidean neighborhood frames (`Frame.IsSerial` and `Frame.IsEuclidean`).
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicED5

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.IsEuclidean]
  : A ∈ LogicED5 → F ⊧ A := Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
theorem consistent : (@LogicED5 α).IsConsistent := by
  by_contra! hC
  simpa using LogicED5.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicED5 α)) :=
  MaximalConsistentSet.nonempty consistent

end LogicED5


theorem LogicED_ssubset_LogicED5 : @LogicED ℕ ⊂ LogicED5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicED ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomFive
      (LogicED.sound frame_1_0 hFive)

theorem LogicE5_ssubset_LogicED5 : @LogicE5 ℕ ⊂ LogicED5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hD : Axioms.D #0 ∈ (@LogicE5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD
      (LogicE5.sound frame_1_3 hD)

end
