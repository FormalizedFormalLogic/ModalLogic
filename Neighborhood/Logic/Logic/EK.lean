module

public import Neighborhood.Logic.Logic.E
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame4_11259170869739560

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEK

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.HasPropertyK] :
    A ∈ LogicEK → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, _, rfl⟩; simp)

instance : (@LogicEK α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEK.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEK α) := by
  by_contra! hcon
  exact frame_4_11259170869739560.not_valid_axiomM hab (LogicEK.sound _ (hcon (#a ⋎ #b) #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEK α) := by
  by_contra! hcon
  exact frame_4_11259170869739560.not_valid_axiomC hab (LogicEK.sound _ (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEK α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEK.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEK α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEK.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEK α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEK.sound frame_1_0 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEK α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEK.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEK α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicEK.sound frame_1_1 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEK α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicEK.sound frame_1_1 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEK α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEK.sound frame_1_0 (hcon #a))

end LogicEK

theorem LogicEK.ssubset_LogicE : @LogicE ℕ ⊂ LogicEK := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · obtain ⟨A, B, hA⟩ := LogicE.not_provable_axiomK (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.K A B, (ProvableHilbert.axm (by grind)), hA⟩

end
