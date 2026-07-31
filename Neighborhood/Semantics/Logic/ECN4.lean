module

public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Logic.EC4
public import Neighborhood.Semantics.Logic.EN4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_137
public import Neighborhood.Semantics.Example.Frame3_10520744

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
instance : (@LogicECN4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECN4.sound frame_1_2 hC⟩

end LogicECN4

theorem LogicECN_ssubset_LogicECN4 : @LogicECN ℕ ⊂ LogicECN4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicECN ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_137.not_valid_axiomFour
      (LogicECN.sound frame_2_137 hFour)

theorem LogicEC4_ssubset_LogicECN4 : @LogicEC4 ℕ ⊂ LogicECN4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ (@LogicEC4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicEC4.sound frame_1_0 hN)

theorem LogicEN4_ssubset_LogicECN4 : @LogicEN4 ℕ ⊂ LogicECN4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ (@LogicEN4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_10520744.not_valid_axiomC (LogicEN4.sound frame_3_10520744 hC)

end
