module

public import Neighborhood.Semantics.Logic.ED
import Neighborhood.Semantics.Example.Frame1_2
import Neighborhood.Semantics.Example.Frame1_1

/-!
# The neighborhood logic `LogicET`

Soundness, consistency and completeness of `LogicET`, the classical modal logic axiomatised by
the reflexivity axiom `T`, with respect to the reflexive neighborhood frames
(`Frame.IsReflexive`), and the strict inclusion of `LogicED` in `LogicET`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicET.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsReflexive] :
    A ∈ LogicET → F ⊧ A :=
  Hilbert.sound (fun _ hB => by obtain ⟨_, rfl⟩ := hB; exact valid_axiomT_of_isReflexive)

theorem LogicET.consistent : (@LogicET α).IsConsistent := by
  by_contra! hC
  simpa using LogicET.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicET α)) :=
  MaximalConsistentSet.nonempty LogicET.consistent

variable [DecidableEq α]

theorem LogicET.complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsReflexive] → F ⊧ A) :
    A ∈ @LogicET α :=
  (basicCanonicity LogicET).mem_of_valid
    (h (basicCanonicity LogicET).toModel.toFrame
      (basicCanonicity LogicET).toModel.Val)


theorem LogicED_ssubset_LogicET : @LogicED ℕ ⊂ LogicET := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ⟨A, rfl⟩
    exact Logic.C_trans Logic.axiomT Logic.diaTc
  · intro h
    have hT : Axioms.T #0 ∈ @LogicED ℕ := h (ProvableHilbert.axm ⟨_, rfl⟩)
    exact frame_1_1.not_isReflexive (isReflexive_of_valid_axiomT (LogicED.sound frame_1_1 hT))

end
