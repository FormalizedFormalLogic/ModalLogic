module

public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_90
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_43176
public import Neighborhood.Semantics.Example.Frame3_8421506

/-!
# The neighborhood logic `LogicED4`

Soundness and consistency of `LogicED4`, the classical modal logic axiomatised by
the seriality axiom `D` and the transitivity axiom `Four`, with respect to
the serial and transitive neighborhood frames (`Frame.IsSerial` and `Frame.IsTransitive`).
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicED4

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.IsTransitive]
  : A ∈ LogicED4 → F ⊧ A := Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicED4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicED4.sound frame_1_2 hC⟩

lemma not_provable_axiomC (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicED4 α) := by
  by_contra! hcon
  exact frame_3_43176.not_valid_axiomC hab (LogicED4.sound frame_3_43176 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicED4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicED4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomM (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicED4 α) := by
  by_contra! hcon
  exact frame_3_8421506.not_valid_axiomM hab (LogicED4.sound frame_3_8421506 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicED4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicED4.sound frame_1_0 hcon)

omit [DecidableEq α] in
lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicED4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicED4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomK (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicED4 α) := by
  by_contra! hcon
  exact frame_3_43176.not_valid_axiomK hab (LogicED4.sound frame_3_43176 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicED4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicED4.sound frame_1_0 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicED4 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomP (LogicED4.sound frame_2_90 hcon)

end LogicED4


theorem LogicED_ssubset_LogicED4 : @LogicED ℕ ⊂ LogicED4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicED.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicE4_ssubset_LogicED4 : @LogicE4 ℕ ⊂ LogicED4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, hA⟩ := LogicE4.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
