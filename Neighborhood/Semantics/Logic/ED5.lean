module

public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.E5
public import Neighborhood.Semantics.Example.Frame2_90

/-!
# The neighborhood logic `LogicED5`

Soundness and consistency of `LogicED5`, the classical modal logic axiomatised by
the seriality axiom `D` and the Euclideanity axiom `Five`, with respect to
the serial and Euclidean neighborhood frames (`Frame.IsSerial` and `Frame.IsEuclidean`).
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicED5

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.IsEuclidean]
  : A ∈ LogicED5 → F ⊧ A := Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicED5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicED5.sound frame_1_2 hC⟩

lemma not_provable_axiomC {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicED5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomC hab (LogicED5.sound frame_3_10528928 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomFour {a : α} : ∃ A, Axioms.Four A ∉ (@LogicED5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomFour (LogicED5.sound frame_3_10528928 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicED5 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomN (LogicED5.sound frame_2_90 hcon)

end LogicED5


theorem LogicED_ssubset_LogicED5 : @LogicED ℕ ⊂ LogicED5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicED.not_provable_axiomFive (a := (0 : ℕ))
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicE5_ssubset_LogicED5 : @LogicE5 ℕ ⊂ LogicED5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, hA⟩ := LogicE5.not_provable_axiomD (a := (0 : ℕ))
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
