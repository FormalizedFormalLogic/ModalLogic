module

public import Neighborhood.Logic.Logic.EN4
public import Neighborhood.Logic.Logic.EN5
public import Neighborhood.Logic.Logic.E45
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_153
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame2_206

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEN45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicEN45 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEN45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEN45.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEN45 α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomM hab (LogicEN45.sound frame_2_153 (hcon #a #b))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEN45 α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomK hab (LogicEN45.sound frame_2_153 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEN45 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicEN45.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEN45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEN45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEN45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEN45.sound frame_2_170 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEN45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEN45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEN45 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEN45.sound frame_1_3 hcon)

end LogicEN45

theorem LogicEN45.ssubset_LogicEN4 : @LogicEN4 ℕ ⊂ LogicEN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEN4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEN45.ssubset_LogicEN5 : @LogicEN5 ℕ ⊂ LogicEN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEN5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEN45.ssubset_LogicE45 : @LogicE45 ℕ ⊂ LogicEN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicE45.not_provable_axiomN⟩

end
