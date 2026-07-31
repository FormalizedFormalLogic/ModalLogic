module

public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Logic.E5
public import Neighborhood.Semantics.Example.Frame2_153
public import Neighborhood.Semantics.Example.Frame2_186
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_170

/-!
# The neighborhood logic `LogicEN5`

Soundness and consistency of `LogicEN5`, the classical modal logic axiomatised by
`N := □⊤` and the Euclideanity axiom `5` over `LogicE`, with respect to the
frames containing their unit and being Euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEN5

theorem sound {κ} [Nonempty κ] (F : Frame κ)
    [F.ContainsUnit] [F.IsEuclidean] :
    A ∈ LogicEN5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEN5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEN5.sound frame_1_2 hC⟩

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEN5 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicEN5.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEN5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEN5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEN5 α) := by
  by_contra! hcon
  exact frame_2_186.not_valid_axiomFour
    (LogicEN5.sound frame_2_186 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEN5 α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomM hab (LogicEN5.sound frame_2_153 (hcon #a #b))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEN5 α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomK hab (LogicEN5.sound frame_2_153 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEN5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEN5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEN5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEN5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEN5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEN5.sound frame_1_3 hcon)

end LogicEN5

theorem LogicEN_ssubset_LogicEN5 : @LogicEN ℕ ⊂ LogicEN5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEN.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicE5_ssubset_LogicEN5 : @LogicE5 ℕ ⊂ LogicEN5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicE5.not_provable_axiomN⟩

end
