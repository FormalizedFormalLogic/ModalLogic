module

public import Neighborhood.Logic.Logic.EC
public import Neighborhood.Logic.Logic.ED
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_9471106

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECD

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial] :
    A ∈ LogicECD → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECD α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECD.sound frame_1_2 hC⟩

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicECD.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicECD.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECD α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicECD.sound frame_1_1 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECD α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicECD.sound frame_1_1 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECD α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomK hab (LogicECD.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECD α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomM hab (LogicECD.sound frame_1_1 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECD α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicECD.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECD α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicECD.sound frame_2_140 (hcon #a))

theorem ssubset_LogicEC : @LogicEC ℕ ⊂ LogicECD := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEC.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicED : @LogicED ℕ ⊂ LogicECD := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicED.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsRegular] → [F.IsSerial] → F ⊧ A) :
    A ∈ @LogicECD α :=
  (basicCanonicalModel LogicECD).mem_of_valid
    (h (basicCanonicalModel LogicECD).toFrame
      (basicCanonicalModel LogicECD).Val)

end LogicECD

end
