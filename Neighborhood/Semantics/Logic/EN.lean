module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0

/-!
# The neighborhood logic `LogicEN`

Soundness, consistency and completeness of `LogicEN`, the classical modal logic axiomatized by
`N := □⊤` over `LogicE`, with respect to the frames containing their unit
(`Frame.ContainsUnit`).
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEN.sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] :
    A ∈ @LogicEN α → F ⊧ A :=
  Hilbert.sound (by rintro _ rfl; simp)

instance : (@LogicEN α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEN.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem LogicEN.complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → F ⊧ A) :
    A ∈ @LogicEN α :=
  (basicCanonicalModel LogicEN).mem_of_valid
    (h (basicCanonicalModel LogicEN).toFrame
      (basicCanonicalModel LogicEN).Val)


theorem LogicE_ssubset_LogicEN : @LogicE ℕ ⊂ LogicEN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicE ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicE.sound frame_1_0 hN)

end
