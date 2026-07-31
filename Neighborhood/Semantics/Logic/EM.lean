module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Supplementation
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame3_137264

/-!
# The neighborhood logic `LogicEM`

Soundness, consistency and completeness of `LogicEM`, the classical modal logic axiomatised by
the monotonicity axiom `M`, with respect to all monotonic neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEM.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] :
    A ∈ LogicEM → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, _, rfl⟩; simp)

instance : (@LogicEM α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEM.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem LogicEM.complete (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → F ⊧ A) :
    A ∈ @LogicEM α :=
  (supplementedBasicCanonicalModel LogicEM).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEM).toFrame
      (supplementedBasicCanonicalModel LogicEM).Val)


theorem LogicE_ssubset_LogicEM : @LogicE ℕ ⊂ LogicEM := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicE ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_137264.not_valid_axiomM (LogicE.sound _ hM)

end
