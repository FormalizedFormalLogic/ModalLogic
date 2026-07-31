module

public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Logic.EC5
public import Neighborhood.Semantics.Logic.EN5
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_75
public import Neighborhood.Semantics.Example.Frame2_137
public import Neighborhood.Semantics.Example.Frame2_206

/-!
# The neighborhood logic `LogicECN5`

Soundness and consistency of `LogicECN5`, the classical modal logic axiomatised by `C`, `N := □⊤`
and the Euclideanness axiom `Five` over `LogicE`, with respect to regular neighborhood frames that
contain their unit and are Euclidean.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicECN5

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsRegular] [F.IsEuclidean]
  : A ∈ LogicECN5 → F ⊧ A := Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
theorem consistent : (@LogicECN5 α).IsConsistent := by
  by_contra! hC
  simpa using LogicECN5.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECN5 α)) :=
  MaximalConsistentSet.nonempty consistent

end LogicECN5

theorem LogicECN_ssubset_LogicECN5 : @LogicECN ℕ ⊂ LogicECN5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicECN ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_137.not_valid_axiomFive
      (LogicECN.sound frame_2_137 hFive)

theorem LogicEC5_ssubset_LogicECN5 : @LogicEC5 ℕ ⊂ LogicECN5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ (@LogicEC5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_75.not_valid_axiomN (LogicEC5.sound frame_2_75 hN)

theorem LogicEN5_ssubset_LogicECN5 : @LogicEN5 ℕ ⊂ LogicECN5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ (@LogicEN5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_206.not_valid_axiomC (LogicEN5.sound frame_2_206 hC)

end
