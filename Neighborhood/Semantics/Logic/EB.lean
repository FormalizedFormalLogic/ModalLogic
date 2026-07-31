module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_9488552

/-!
# The neighborhood logic `LogicEB`

Soundness, consistency and completeness of `LogicEB`, the classical modal logic axiomatised by
the symmetry axiom `B`, with respect to the symmetric neighborhood frames, and the strict
inclusion of `LogicE` in `LogicEB`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSymmetric] :
    A ∈ LogicEB → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, rfl⟩; simp)

instance : (@LogicEB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEB.sound frame_1_2 hC⟩

section

variable [DecidableEq α]

/-- Neither the smallest nor the largest canonical model is symmetric, but the intermediate one
of `intermediateRelativeMaximalCanonicalModel` is.

- [Che80, Exercise 9.39(b)] -/
theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsSymmetric] → F ⊧ A) :
    A ∈ @LogicEB α :=
  (intermediateRelativeMaximalCanonicalModel LogicEB).mem_of_valid
    (h (intermediateRelativeMaximalCanonicalModel LogicEB).toFrame
      (intermediateRelativeMaximalCanonicalModel LogicEB).Val)

end

lemma not_provable_axiomC [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEB α) := by
  by_contra! hcon
  exact frame_3_9488552.not_valid_axiomC hab (LogicEB.sound frame_3_9488552 (hcon #a #b))

lemma not_provable_axiomD {a : α} : ∃ A, Axioms.D A ∉ (@LogicEB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD
    (LogicEB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomN (LogicEB.sound frame_1_1 hcon)

end LogicEB

theorem LogicE_ssubset_LogicEB : (@LogicE ℕ) ⊂ LogicEB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · obtain ⟨A, hA⟩ := LogicE.not_provable_axiomB (a := (0 : ℕ))
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

end
