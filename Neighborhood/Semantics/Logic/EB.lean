module

public import Neighborhood.Semantics.Logic.E
import Neighborhood.Semantics.Example.SimpleBlackhole
import Neighborhood.Semantics.Example.SimpleWhitehole

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
  Hilbert.sound (fun _ hB => by obtain ⟨_, rfl⟩ := hB; exact valid_axiomB_of_isSymmetric)

theorem LogicEB.consistent : (@LogicEB α).IsConsistent := by
  by_contra! hC
  simpa using LogicEB.sound Frame.simple_blackhole hC


theorem LogicE_ssubset_LogicEB : (@LogicE ℕ) ⊂ LogicEB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hB : Axioms.B (.atom 0) ∈ (@LogicE ℕ) := h (ProvableHilbert.axm ⟨_, rfl⟩)
    have hS : Frame.simple_whitehole.IsSymmetric := isSymmetric_of_valid_axiomB (LogicE.sound _ hB)
    have := hS.symm {()} (show () ∈ _ by simp)
    simp [Frame.box] at this

end
