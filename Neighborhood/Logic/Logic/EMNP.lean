module

public import Neighborhood.Logic.Logic.EMN
public import Neighborhood.Logic.Logic.EMP
public import Neighborhood.Logic.Logic.ENP
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame2_206

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMNP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.ContainsUnit]
    [F.NotContainsEmpty] :
    A ∈ LogicEMNP → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | rfl) <;> simp)

instance : (@LogicEMNP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMNP.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] →
      [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicEMNP α :=
  (supplementedBasicCanonicalModel LogicEMNP).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMNP).toFrame
      (supplementedBasicCanonicalModel LogicEMNP).Val)

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMNP α) := by
  by_contra! hcon
  exact frame_2_238.not_valid_axiomD (LogicEMNP.sound frame_2_238 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMNP α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicEMNP.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMNP α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicEMNP.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMNP α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEMNP.sound frame_2_140 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMNP α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEMNP.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMNP α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEMNP.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMNP α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEMNP.sound frame_2_138 (hcon #a))

end LogicEMNP

theorem LogicEMNP.ssubset_LogicEMP : @LogicEMP ℕ ⊂ LogicEMNP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by rintro A (⟨B, C, rfl⟩ | rfl) <;> grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEMP.not_provable_axiomN⟩

theorem LogicEMNP.ssubset_LogicEMN : @LogicEMN ℕ ⊂ LogicEMNP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · exact ⟨Axioms.P, (ProvableHilbert.axm (by grind)), LogicEMN.not_provable_axiomP⟩

theorem LogicEMNP.ssubset_LogicENP : @LogicENP ℕ ⊂ LogicEMNP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.union_subset_union_left _ Set.subset_union_right)
  · obtain ⟨A, B, hA⟩ := LogicENP.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
