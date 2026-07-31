module

public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Logic.E5
public import Neighborhood.Semantics.Example.Frame2_137
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_75

/-!
# The neighborhood logic `LogicEN5`

Soundness and consistency of `LogicEN5`, the classical modal logic axiomatised by
`N := □⊤` and the Euclideanity axiom `5` over `LogicE`, with respect to the
frames containing their unit and being Euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEN5

theorem sound {κ} [Nonempty κ] (F : Frame κ)
    [F.ContainsUnit] [F.IsEuclidean] :
    A ∈ LogicEN5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEN5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEN5.sound frame_1_2 hC⟩

end LogicEN5

theorem LogicEN_ssubset_LogicEN5 : @LogicEN ℕ ⊂ LogicEN5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEN ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_137.not_valid_axiomFive (LogicEN.sound frame_2_137 hFive)

theorem LogicE5_ssubset_LogicEN5 : @LogicE5 ℕ ⊂ LogicEN5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicE5 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_75.not_valid_axiomN (LogicE5.sound frame_2_75 hN)

end
