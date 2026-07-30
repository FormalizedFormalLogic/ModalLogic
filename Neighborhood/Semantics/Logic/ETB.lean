module

public import Neighborhood.Semantics.Logic.ET
public import Neighborhood.Semantics.Logic.EB
import Neighborhood.Semantics.Example.Frame1_2
import Neighborhood.Semantics.Example.Frame1_0

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
  Hilbert.sound
    (fun _ hB => by
      rcases hB with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact valid_axiomT_of_isReflexive
      · exact valid_axiomB_of_isSymmetric)

theorem LogicETB.consistent : (@LogicETB α).IsConsistent := by
  by_contra! hC
  simpa using LogicETB.sound frame_1_2 hC

theorem LogicET_ssubset_LogicETB : @LogicET ℕ ⊂ LogicETB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hB : Axioms.B (.atom 0) ∈ @LogicET ℕ := h (ProvableHilbert.axm (Or.inr ⟨_, rfl⟩))
    have hS := isSymmetric_of_valid_axiomB (LogicET.sound frame_1_0 hB)
    have := hS.symm (X := Set.univ)
    simp [Frame.box, Frame.dia] at this

theorem LogicEB_ssubset_LogicETB : @LogicEB ℕ ⊂ LogicETB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hT : Axioms.T (.atom 0) ∈ @LogicEB ℕ := h (ProvableHilbert.axm (Or.inl ⟨_, rfl⟩))
    haveI : (⟨fun _ => Set.univ⟩ : Frame (Fin 1)).IsSymmetric := ⟨fun X => by simp [Frame.box]⟩
    have hR := isReflexive_of_valid_axiomT
      (LogicEB.sound (⟨fun _ => Set.univ⟩ : Frame (Fin 1)) hT)
    have := hR.refl (∅ : Set (Fin 1)) (show (0 : Fin 1) ∈ _ by simp [Frame.box])
    simp at this

end
