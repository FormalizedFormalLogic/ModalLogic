module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.AxiomN

/-!
# The neighborhood logic `LogicEN`

Soundness, consistency and completeness of `LogicEN`, the classical modal logic axiomatized by
`N := □⊤` over `LogicE`, with respect to the frames containing their unit
(`Frame.ContainsUnit`). Also its strict inclusion in `LogicE`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

/-! ### Soundness, consistency and completeness -/

/-- `LogicEN` is sound with respect to every frame containing its unit. -/
theorem LogicEN.sound (h : A ∈ @LogicEN α) {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] :
    F ⊧ A :=
  Hilbert.sound (fun B hB => by simp only [Set.mem_singleton_iff] at hB; grind) h

instance : (@LogicEN α).Consistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole)
    (fun B hB => by simp only [Set.mem_singleton_iff] at hB; grind)

variable [DecidableEq α]

/-- `LogicEN` is complete with respect to all frames containing their unit. -/
theorem LogicEN.complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), F.ContainsUnit → F ⊧ A) :
    A ∈ @LogicEN α :=
  (basicCanonicity LogicEN).mem_of_valid
    (h (basicCanonicity LogicEN).toModel.toFrame inferInstance
      (basicCanonicity LogicEN).toModel.Val)

/-! ### Strict inclusion in `LogicE` -/

theorem LogicE_ssubset_LogicEN : @LogicE ℕ ⊂ LogicEN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicE ℕ := h (ProvableHilbert.axm rfl)
    exact Frame.simple_whitehole.not_valid_axiomN (LogicE.sound hN Frame.simple_whitehole)

end
