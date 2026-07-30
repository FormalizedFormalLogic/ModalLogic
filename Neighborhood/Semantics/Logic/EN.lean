module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.AxiomN
import Neighborhood.Semantics.Example.SimpleBlackhole
import Neighborhood.Semantics.Example.SimpleWhitehole

/-!
# The neighborhood logic `LogicEN`

Soundness, consistency and completeness of `LogicEN`, the classical modal logic axiomatized by
`N := □⊤` over `LogicE`, with respect to the frames containing their unit
(`Frame.ContainsUnit`). Also its strict inclusion in `LogicE`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEN.sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] :
    A ∈ @LogicEN α → F ⊧ A :=
  Hilbert.sound (fun B hB => by simp only [Set.mem_singleton_iff] at hB; grind)

theorem LogicEN.consistent : (@LogicEN α).IsConsistent := by
  by_contra! hC
  simpa using LogicEN.sound Frame.simple_blackhole hC

instance : Nonempty (MaximalConsistentSet (@LogicEN α)) :=
  MaximalConsistentSet.nonempty LogicEN.consistent

variable [DecidableEq α]

theorem LogicEN.complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → F ⊧ A) :
    A ∈ @LogicEN α :=
  (basicCanonicity LogicEN).mem_of_valid
    (h (basicCanonicity LogicEN).toModel.toFrame
      (basicCanonicity LogicEN).toModel.Val)


theorem LogicE_ssubset_LogicEN : @LogicE ℕ ⊂ LogicEN := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicE ℕ := h (ProvableHilbert.axm rfl)
    exact Frame.simple_whitehole.not_valid_axiomN (LogicE.sound Frame.simple_whitehole hN)

end
