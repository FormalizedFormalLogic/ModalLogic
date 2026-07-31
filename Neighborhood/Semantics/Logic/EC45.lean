module

public import Neighborhood.Semantics.Logic.EC4
public import Neighborhood.Semantics.Logic.EC5
public import Neighborhood.Semantics.Logic.E45
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_79
public import Neighborhood.Semantics.Example.Frame2_206

/-!
# The neighborhood logic `LogicEC45`

Soundness and consistency of `LogicEC45`, the classical modal logic axiomatised by the regularity
axiom `C`, the transitivity axiom `Four` and the Euclidean axiom `Five`, with respect to the
regular, transitive and Euclidean neighborhood frames. Also proves the strict inclusion of
`LogicEC4` in `LogicEC45`.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicEC45

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicEC45 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicEC45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEC45.sound frame_1_2 hC⟩

end LogicEC45


theorem LogicEC4_ssubset_LogicEC45 : @LogicEC4 ℕ ⊂ LogicEC45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEC4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomFive (LogicEC4.sound frame_1_0 hFive)

theorem LogicEC5_ssubset_LogicEC45 : @LogicEC5 ℕ ⊂ LogicEC45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicEC5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_79.not_valid_axiomFour (LogicEC5.sound frame_2_79 hFour)

theorem LogicE45_ssubset_LogicEC45 : @LogicE45 ℕ ⊂ LogicEC45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ (@LogicE45 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_206.not_valid_axiomC (LogicE45.sound frame_2_206 hC)

end
