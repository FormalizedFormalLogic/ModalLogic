module

public import Neighborhood.Semantics.Logic.E
import Neighborhood.Semantics.Example.Frame1_2
import Neighborhood.Semantics.Example.Frame1_0

/-!
# The neighborhood logic `LogicEB`

Soundness and consistency of `LogicEB`, the classical modal logic axiomatised by the symmetry
axiom `B`, with respect to the symmetric neighborhood frames, and its strict inclusion in
`LogicE`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEB.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSymmetric] :
    A ∈ LogicEB → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, rfl⟩; simp)

theorem LogicEB.consistent : (@LogicEB α).IsConsistent := by
  by_contra! hC
  simpa using LogicEB.sound frame_1_2 hC


theorem LogicE_ssubset_LogicEB : (@LogicE ℕ) ⊂ LogicEB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hB : Axioms.B #0 ∈ (@LogicE ℕ) := h (ProvableHilbert.axm (by grind))
    have hS : frame_1_0.IsSymmetric := isSymmetric_of_valid_axiomB (LogicE.sound _ hB)
    have := hS.symm {0} (show (0 : Fin 1) ∈ _ by simp)
    simp [Frame.box] at this

end
