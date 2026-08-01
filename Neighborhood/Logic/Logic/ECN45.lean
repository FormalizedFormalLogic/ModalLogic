module

public import Neighborhood.Logic.Logic.ECN4
public import Neighborhood.Logic.Logic.ECN5
public import Neighborhood.Logic.Logic.EC45
public import Neighborhood.Logic.Logic.EN45
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_153
public import Neighborhood.Semantics.Example.Frame2_170

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECN45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.ContainsUnit]
    [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicECN45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECN45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECN45.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECN45 α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomM hab (LogicECN45.sound frame_2_153 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECN45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECN45.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECN45 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicECN45.sound frame_2_170 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECN45 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECN45.sound frame_1_3 (hcon #a))

theorem ssubset_LogicECN4 : @LogicECN4 ℕ ⊂ LogicECN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECN4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECN5 : @LogicECN5 ℕ ⊂ LogicECN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicECN5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEC45 : @LogicEC45 ℕ ⊂ LogicECN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · exact ⟨Axioms.N, ProvableHilbert.axm (by grind), LogicEC45.not_provable_axiomN⟩

theorem ssubset_LogicEN45 : @LogicEN45 ℕ ⊂ LogicECN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEN45.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, ProvableHilbert.axm (by grind), hA⟩

end LogicECN45

end
