module

public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.EP
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame2_78

/-!
# The neighborhood logic `LogicET`

Soundness, consistency and completeness of `LogicET`, the classical modal logic axiomatised by
the reflexivity axiom `T`, with respect to the reflexive neighborhood frames
(`Frame.IsReflexive`).
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicET

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsReflexive] :
    A ∈ LogicET → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, rfl⟩; simp)

instance : (@LogicET α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicET.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsReflexive] → F ⊧ A) :
    A ∈ @LogicET α :=
  (basicCanonicalModel LogicET).mem_of_valid
    (h (basicCanonicalModel LogicET).toFrame
      (basicCanonicalModel LogicET).Val)

end LogicET

theorem LogicED_ssubset_LogicET : @LogicED ℕ ⊂ LogicET := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ⟨A, rfl⟩
    exact Logic.C_trans Logic.axiomT Logic.diaTc
  · intro h
    have hT : Axioms.T #0 ∈ @LogicED ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_1.not_isReflexive (isReflexive_of_valid_axiomT (LogicED.sound frame_1_1 hT))

theorem LogicEP_ssubset_LogicET : @LogicEP ℕ ⊂ LogicET := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ rfl
    exact Logic.axiomP
  · intro h
    have hT : (Axioms.T #0 : Formula ℕ) ∈ @LogicEP ℕ := h (Logic.HasAxiomT.T _)
    exact frame_2_78.not_valid_axiomT (LogicEP.sound frame_2_78 hT)

end
