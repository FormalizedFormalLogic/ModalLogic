module

public import Neighborhood.Semantics.Logic.END
public import Neighborhood.Semantics.Logic.ED5
public import Neighborhood.Semantics.Logic.EN5
public import Neighborhood.Semantics.Example.Frame3_8553090

/-!
# The neighborhood logic `LogicEND5`

Soundness and consistency of `LogicEND5`, the classical modal logic axiomatised by `N := □⊤`,
the seriality axiom `D` and the euclidean axiom `Five`, with respect to the unit-containing,
serial and euclidean neighborhood frames.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicEND5

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsSerial]
    [F.IsEuclidean] :
    A ∈ LogicEND5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicEND5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEND5.sound frame_1_2 hC⟩

lemma not_provable_axiomM (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEND5 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicEND5.sound frame_3_8553090 (hcon #a #b))

end LogicEND5

theorem LogicEND_ssubset_LogicEND5 : @LogicEND ℕ ⊂ LogicEND5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEND.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicED5_ssubset_LogicEND5 : @LogicED5 ℕ ⊂ LogicEND5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicED5.not_provable_axiomN⟩

theorem LogicEN5_ssubset_LogicEND5 : @LogicEN5 ℕ ⊂ LogicEND5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEN5.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
