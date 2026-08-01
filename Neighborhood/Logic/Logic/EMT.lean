module

public import Neighborhood.Logic.Logic.ET
public import Neighborhood.Logic.Logic.EMD
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame3_168

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsReflexive] :
    A ∈ LogicEMT → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMT.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsReflexive] → F ⊧ A) :
    A ∈ @LogicEMT α :=
  (supplementedBasicCanonicalModel LogicEMT).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMT).toFrame
      (supplementedBasicCanonicalModel LogicEMT).Val)

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMT α) := by
  by_contra! hcon
  exact frame_3_168.not_valid_axiomC hab (LogicEMT.sound frame_3_168 (hcon #a #b))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMT α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour
    (LogicEMT.sound frame_2_8 (hcon #a))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMT α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMT.sound frame_1_0 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMT α) := by
  by_contra! hcon
  exact frame_3_168.not_valid_axiomK hab (LogicEMT.sound frame_3_168 (hcon #a #b))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMT α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMT.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMT α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMT.sound frame_1_0 (hcon #a))

theorem ssubset_LogicET : @LogicET ℕ ⊂ LogicEMT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicET.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMD : @LogicEMD ℕ ⊂ LogicEMT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMD.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end LogicEMT

end
