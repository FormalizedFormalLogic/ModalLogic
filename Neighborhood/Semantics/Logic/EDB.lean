module

public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.EB
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame1_3

/-!
# The neighborhood logic `LogicEDB`

Soundness and consistency of `LogicEDB`, the classical modal logic axiomatised by
the seriality axiom `D` and the symmetry axiom `B`, with respect to
the serial and symmetric neighborhood frames (`Frame.IsSerial` and `Frame.IsSymmetric`).
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicEDB

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.IsSymmetric]
  : A ∈ LogicEDB → F ⊧ A := Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicEDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEDB.sound frame_1_1 hC⟩

end LogicEDB


theorem LogicED_ssubset_LogicEDB : @LogicED ℕ ⊂ LogicEDB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hB : Axioms.B #0 ∈ (@LogicED ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomB
      (LogicED.sound frame_1_0 hB)

theorem LogicEB_ssubset_LogicEDB : @LogicEB ℕ ⊂ LogicEDB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hD : Axioms.D #0 ∈ (@LogicEB ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD
      (LogicEB.sound frame_1_3 hD)

end
