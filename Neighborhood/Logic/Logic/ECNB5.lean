module

public import Neighborhood.Logic.Logic.ENB5
public import Neighborhood.Logic.Logic.ECB5
public import Neighborhood.Logic.Logic.ECN5
public import Neighborhood.Logic.Logic.ECNB
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_186
public import Neighborhood.Semantics.Example.Frame3_9472136

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECNB5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.ContainsUnit] [F.IsSymmetric]
    [F.IsEuclidean] :
    A ∈ LogicECNB5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECNB5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECNB5.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECNB5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicECNB5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECNB5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicECNB5.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECNB5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECNB5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECNB5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECNB5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECNB5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicECNB5.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECNB5 α) := by
  by_contra! hcon
  exact frame_2_186.not_valid_axiomFour (LogicECNB5.sound frame_2_186 (hcon #a))

theorem ssubset_LogicECB5 : @LogicECB5 ℕ ⊂ LogicECNB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · exact ⟨Axioms.N, ProvableHilbert.axm (by grind), LogicECB5.not_provable_axiomN⟩

theorem ssubset_LogicECN5 : @LogicECN5 ℕ ⊂ LogicECNB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECN5.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicECNB : @LogicECNB ℕ ⊂ LogicECNB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECNB.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicENB5 : @LogicENB5 ℕ ⊂ LogicECNB5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicENB5.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, ProvableHilbert.axm (by grind), hA⟩

end LogicECNB5

end
