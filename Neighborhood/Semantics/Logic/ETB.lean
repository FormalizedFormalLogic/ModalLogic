module

public import Neighborhood.Semantics.Logic.ET
public import Neighborhood.Semantics.Logic.EB
import Neighborhood.Semantics.Example.Frame1_2
import Neighborhood.Semantics.Example.Frame1_0
import Neighborhood.Semantics.Example.Frame1_3

/-!
# The neighborhood logic `LogicETB`

Soundness and consistency of `LogicETB`, the classical modal logic axiomatised by both the
reflexivity axiom `T` and the symmetry axiom `B`, with respect to the neighborhood frames that
are both reflexive and symmetric, and its strict inclusions in `LogicET` and `LogicEB`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicETB.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsReflexive]
    [F.IsSymmetric] :
    A ∈ LogicETB → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

theorem LogicETB.consistent : (@LogicETB α).IsConsistent := by
  by_contra! hC
  simpa using LogicETB.sound frame_1_2 hC

theorem LogicET_ssubset_LogicETB : @LogicET ℕ ⊂ LogicETB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hB : Axioms.B #0 ∈ @LogicET ℕ := h (ProvableHilbert.axm (by grind))
    have hS := isSymmetric_of_valid_axiomB (LogicET.sound frame_1_0 hB)
    have := hS.symm (X := Set.univ)
    simp [Frame.box, Frame.dia] at this

theorem LogicEB_ssubset_LogicETB : @LogicEB ℕ ⊂ LogicETB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hT : Axioms.T #0 ∈ @LogicEB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_isReflexive (isReflexive_of_valid_axiomT (LogicEB.sound frame_1_3 hT))

end
