module

public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Logic.ENB
public import Neighborhood.Semantics.Logic.ECB
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_95
public import Neighborhood.Semantics.Example.Frame2_137
public import Neighborhood.Semantics.Example.Frame3_9488552

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

theorem LogicENB_ssubset_LogicECNB : @LogicENB ℕ ⊂ LogicECNB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ (@LogicENB ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_9488552.not_valid_axiomC (LogicENB.sound frame_3_9488552 hC)

theorem LogicECB_ssubset_LogicECNB : @LogicECB ℕ ⊂ LogicECNB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ (@LogicECB ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_95.not_valid_axiomN (LogicECB.sound frame_2_95 hN)

end
