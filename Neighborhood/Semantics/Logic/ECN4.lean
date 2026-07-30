module

public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_137

/-!
# The neighborhood logic `LogicECN4`

Soundness and consistency of `LogicECN4`, the classical modal logic axiomatised by `C`, `N := □⊤`
and the transitivity axiom `Four` over `LogicE`, with respect to regular neighborhood frames that
contain their unit and are transitive.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicECN4

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsRegular] [F.IsTransitive]
  : A ∈ LogicECN4 → F ⊧ A := Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
theorem consistent : (@LogicECN4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicECN4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECN4 α)) :=
  MaximalConsistentSet.nonempty consistent

end LogicECN4

theorem LogicECN_ssubset_LogicECN4 : @LogicECN ℕ ⊂ LogicECN4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicECN ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_137.not_valid_axiomFour
      (LogicECN.sound frame_2_137 hFour)

end
