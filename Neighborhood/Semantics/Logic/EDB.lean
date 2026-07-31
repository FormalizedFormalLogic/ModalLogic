module

public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.EB
public import Neighborhood.Semantics.Example.Frame3_3346281

/-!
# The neighborhood logic `LogicEDB`

Soundness and consistency of `LogicEDB`, the classical modal logic axiomatised by
the seriality axiom `D` and the symmetry axiom `B`, with respect to
the serial and symmetric neighborhood frames (`Frame.IsSerial` and `Frame.IsSymmetric`).
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicEDB

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.IsSymmetric]
  : A ∈ LogicEDB → F ⊧ A := Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicEDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEDB.sound frame_1_1 hC⟩

lemma not_provable_axiomC {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEDB α) := by
  by_contra! hcon
  exact frame_3_3346281.not_valid_axiomC hab (LogicEDB.sound frame_3_3346281 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEDB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomN (LogicEDB.sound frame_1_1 hcon)

end LogicEDB


theorem LogicED_ssubset_LogicEDB : @LogicED ℕ ⊂ LogicEDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicED.not_provable_axiomB (a := (0 : ℕ))
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEB_ssubset_LogicEDB : @LogicEB ℕ ⊂ LogicEDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, hA⟩ := LogicEB.not_provable_axiomD (a := (0 : ℕ))
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
