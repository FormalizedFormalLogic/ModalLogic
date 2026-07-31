module

public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Logic.EB
public import Neighborhood.Semantics.Example.Frame2_140

/-!
# The neighborhood logic `LogicENB`

Soundness, consistency and completeness of `LogicENB`, the classical modal logic axiomatised by
`N := □⊤` and the symmetry axiom `B` over `LogicE`, with respect to the neighborhood frames that
contain their unit and are symmetric.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsSymmetric] :
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
theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.IsSymmetric] → F ⊧ A) :
    A ∈ @LogicENB α :=
  (intermediateRelativeMaximalCanonicalModel LogicENB).mem_of_valid
    (h (intermediateRelativeMaximalCanonicalModel LogicENB).toFrame
      (intermediateRelativeMaximalCanonicalModel LogicENB).Val)

end

lemma not_provable_axiomC [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENB α) := by
  by_contra! hcon
  exact frame_3_9488552.not_valid_axiomC hab (LogicENB.sound frame_3_9488552 (hcon #a #b))

lemma not_provable_axiomD {a : α} : ∃ A, Axioms.D A ∉ (@LogicENB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicENB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFour {a : α} : ∃ A, Axioms.Four A ∉ (@LogicENB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour
    (Hilbert.sound (F := frame_2_140) (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp) (hcon #a))

end LogicENB

theorem LogicEN_ssubset_LogicENB : @LogicEN ℕ ⊂ LogicENB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEN.not_provable_axiomB (a := (0 : ℕ))
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEB_ssubset_LogicENB : @LogicEB ℕ ⊂ LogicENB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEB.not_provable_axiomN⟩

end
