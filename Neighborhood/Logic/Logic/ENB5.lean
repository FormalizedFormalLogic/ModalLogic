module

public import Neighborhood.Logic.Logic.ENB
public import Neighborhood.Logic.Logic.EN5
public import Neighborhood.Logic.Logic.EB5
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_186
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_11570344

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENB5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsSymmetric]
    [F.IsEuclidean] :
    A ∈ LogicENB5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicENB5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENB5.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENB5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicENB5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENB5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicENB5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENB5 α) := by
  by_contra! hcon
  exact frame_3_11570344.not_valid_axiomC hab (LogicENB5.sound frame_3_11570344 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicENB5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicENB5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicENB5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicENB5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicENB5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicENB5.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENB5 α) := by
  by_contra! hcon
  exact frame_2_186.not_valid_axiomFour (LogicENB5.sound frame_2_186 (hcon #a))

theorem ssubset_LogicEB5 : @LogicEB5 ℕ ⊂ LogicENB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · have hA := LogicEB5.not_provable_axiomN (α := ℕ)
    exact ⟨Axioms.N, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicEN5 : @LogicEN5 ℕ ⊂ LogicENB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEN5.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicENB : @LogicENB ℕ ⊂ LogicENB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicENB.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, ProvableHilbert.axm (by grind), hA⟩

end LogicENB5

end
