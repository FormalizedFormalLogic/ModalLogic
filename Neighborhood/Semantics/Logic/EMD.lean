module

public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame1_3

/-!
# The neighborhood logic `LogicEMD`

Soundness and consistency of `LogicEMD`, the classical modal logic axiomatised by the
monotonicity axiom `M` and the seriality axiom `D`, with respect to the monotonic and
serial neighborhood frames.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicEMD

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSerial] :
    A ∈ LogicEMD → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
theorem consistent : (@LogicEMD α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMD.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMD α)) :=
  MaximalConsistentSet.nonempty LogicEMD.consistent

end LogicEMD

theorem LogicED_ssubset_LogicEMD : @LogicED ℕ ⊂ LogicEMD := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicED ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_1.not_valid_axiomM (LogicED.sound frame_1_1 hM)

theorem LogicEM_ssubset_LogicEMD : @LogicEM ℕ ⊂ LogicEMD := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hD : Axioms.D #0 ∈ (@LogicEM ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_isSerial (isSerial_of_valid_axiomD (LogicEM.sound frame_1_3 hD))

end
