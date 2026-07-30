module

public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_137

/-!
# The neighborhood logic `LogicECNB`

Soundness and consistency of `LogicECNB`, the classical modal logic axiomatised by `C`, `N := □⊤`
and the symmetry axiom `B` over `LogicE`, with respect to regular neighborhood frames that
contain their unit and are symmetric.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicECNB

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsRegular] [F.IsSymmetric]
  : A ∈ LogicECNB → F ⊧ A := Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
theorem consistent : (@LogicECNB α).IsConsistent := by
  by_contra! hC
  simpa using LogicECNB.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECNB α)) :=
  MaximalConsistentSet.nonempty consistent

end LogicECNB

theorem LogicECN_ssubset_LogicECNB : @LogicECN ℕ ⊂ LogicECNB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hB : Axioms.B #0 ∈ (@LogicECN ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_137.not_valid_axiomB
      (LogicECN.sound frame_2_137 hB)

end
