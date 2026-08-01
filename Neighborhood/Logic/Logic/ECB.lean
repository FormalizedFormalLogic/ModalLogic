module

public import Neighborhood.Logic.Logic.EB
public import Neighborhood.Logic.Logic.EC
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame2_95
public import Neighborhood.Semantics.Example.Frame3_9472136

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSymmetric] :
    A ∈ LogicECB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECB.sound frame_1_2 hC⟩

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECB α) := by
  intro hcon
  exact frame_2_95.not_valid_axiomN (LogicECB.sound frame_2_95 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECB α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomK hab (LogicECB.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECB α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomM hab (LogicECB.sound frame_1_1 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECB α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicECB.sound frame_1_1 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECB α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicECB.sound frame_1_1 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicECB.sound frame_2_140 (hcon #a))

end LogicECB

theorem LogicECB.ssubset_LogicEC : (@LogicEC ℕ) ⊂ LogicECB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEC.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECB.ssubset_LogicEB : @LogicEB ℕ ⊂ LogicECB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicEB.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
