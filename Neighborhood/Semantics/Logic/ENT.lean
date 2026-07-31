module

public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Logic.END
public import Neighborhood.Semantics.Logic.ET
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_170

/-!
# The neighborhood logic `LogicENT`

Soundness, consistency and completeness of `LogicENT`, the classical modal logic axiomatised by
`N := □⊤` and the reflexivity axiom `T` over `LogicE`, with respect to the neighborhood frames
that contain their unit and are reflexive.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsReflexive] :
    A ∈ LogicENT → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp)

instance : (@LogicENT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENT.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.IsReflexive] → F ⊧ A) :
    A ∈ @LogicENT α :=
  (basicCanonicalModel LogicENT).mem_of_valid
    (h (basicCanonicalModel LogicENT).toFrame
      (basicCanonicalModel LogicENT).Val)

end LogicENT

theorem LogicET_ssubset_LogicENT : @LogicET ℕ ⊂ LogicENT := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicET ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicET.sound frame_1_0 hN)

theorem LogicEND_ssubset_LogicENT : @LogicEND ℕ ⊂ LogicENT := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (rfl | ⟨B, rfl⟩)
    · exact Logic.axiomN
    · exact Logic.axiomD
  · intro h
    have hT : Axioms.T #0 ∈ @LogicEND ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomT (LogicEND.sound frame_2_170 hT)

end
