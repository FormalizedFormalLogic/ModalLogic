module

public import Neighborhood.Semantics.Logic.ED

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

instance : Frame.simple_blackhole.IsReflexive where
  refl X x hx := by
    simp only [Frame.box, Frame.simple_blackhole, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
    subst hx
    trivial

theorem LogicET.consistent : (@LogicET α).IsConsistent := by
  by_contra! hC
  simpa using LogicET.sound Frame.simple_blackhole hC

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
    have hT : Axioms.T (.atom 0) ∈ @LogicED ℕ := h (ProvableHilbert.axm ⟨_, rfl⟩)
    haveI : (⟨fun _ => {∅}⟩ : Frame (Fin 1)).IsSerial :=
      ⟨fun X x hx => by simp_all [Frame.dia, Frame.box]⟩
    have hR := isReflexive_of_valid_axiomT (LogicED.sound (⟨fun _ => {∅}⟩ : Frame (Fin 1)) hT)
    have := hR.refl (∅ : Set (Fin 1)) (show (0 : Fin 1) ∈ _ by simp [Frame.box])
    simp at this

end
