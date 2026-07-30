module

public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame1_3

/-!
# The neighborhood logic `LogicED4`

Soundness and consistency of `LogicED4`, the classical modal logic axiomatised by
the seriality axiom `D` and the transitivity axiom `Four`, with respect to
the serial and transitive neighborhood frames (`Frame.IsSerial` and `Frame.IsTransitive`).
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicED4

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.IsTransitive]
  : A ∈ LogicED4 → F ⊧ A := Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
theorem consistent : (@LogicED4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicED4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicED4 α)) :=
  MaximalConsistentSet.nonempty consistent

end LogicED4


theorem LogicED_ssubset_LogicED4 : @LogicED ℕ ⊂ LogicED4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicED ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_1.not_valid_axiomFour
      (LogicED.sound frame_1_1 hFour)

theorem LogicE4_ssubset_LogicED4 : @LogicE4 ℕ ⊂ LogicED4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hD : Axioms.D #0 ∈ (@LogicE4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD
      (LogicE4.sound frame_1_3 hD)

end
