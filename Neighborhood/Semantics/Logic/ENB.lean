module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Logic.EB
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_170

/-!
# The neighborhood logic `LogicENB`

Soundness, consistency and completeness of `LogicENB`, the classical modal logic axiomatised by
`N := □⊤` and the symmetry axiom `B` over `LogicE`, with respect to the neighborhood frames that
contain their unit and are symmetric.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicENB.sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsSymmetric] :
    A ∈ LogicENB → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp)

instance : (@LogicENB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENB.sound frame_1_2 hC⟩

section

variable [DecidableEq α]

/-- The intermediate canonical model of `intermediateRelativeMaximalCanonicalModel` contains its
unit as well as being symmetric.

- [Che80, Exercise 9.39(b)] -/
theorem LogicENB.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.IsSymmetric] → F ⊧ A) :
    A ∈ @LogicENB α :=
  (intermediateRelativeMaximalCanonicalModel LogicENB).mem_of_valid
    (h (intermediateRelativeMaximalCanonicalModel LogicENB).toFrame
      (intermediateRelativeMaximalCanonicalModel LogicENB).Val)

end


theorem LogicEN_ssubset_LogicENB : @LogicEN ℕ ⊂ LogicENB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hB : Axioms.B #0 ∈ @LogicEN ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomB (LogicEN.sound frame_2_170 hB)

theorem LogicEB_ssubset_LogicENB : @LogicEB ℕ ⊂ LogicENB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_1.not_valid_axiomN (LogicEB.sound frame_1_1 hN)

end
