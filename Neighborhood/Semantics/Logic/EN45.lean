module

public import Neighborhood.Semantics.Logic.EN4
public import Neighborhood.Semantics.Logic.EN5
public import Neighborhood.Semantics.Logic.E45

/-!
# The neighborhood logic `LogicEN45`

Soundness and consistency of `LogicEN45`, the classical modal logic axiomatised by `N := □⊤`,
the transitivity axiom `Four` and the euclidean axiom `Five`, with respect to the unit-containing,
transitive and euclidean neighborhood frames.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicEN45

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicEN45 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicEN45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEN45.sound frame_1_2 hC⟩

lemma not_provable_axiomM (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEN45 α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomM hab (LogicEN45.sound frame_2_153 (hcon #a #b))

end LogicEN45

theorem LogicEN4_ssubset_LogicEN45 : @LogicEN4 ℕ ⊂ LogicEN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEN4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEN5_ssubset_LogicEN45 : @LogicEN5 ℕ ⊂ LogicEN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEN5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicE45_ssubset_LogicEN45 : @LogicE45 ℕ ⊂ LogicEN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicE45.not_provable_axiomN⟩

end
