module

public import Neighborhood.Logic.Logic.END
public import Neighborhood.Logic.Logic.EMD
public import Neighborhood.Logic.Logic.EMNP
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_8421544

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMND

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.ContainsUnit] [F.IsSerial] :
    A ∈ LogicEMND → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMND α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMND.sound frame_1_2 hC⟩

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEMND.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEMND.sound frame_2_140 (hcon #a))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMND α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEMND.sound frame_2_170 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMND α) := by
  by_contra! hcon
  exact frame_3_8421544.not_valid_axiomK hab (LogicEMND.sound frame_3_8421544 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMND α) := by
  by_contra! hcon
  exact frame_3_8421544.not_valid_axiomC hab (LogicEMND.sound frame_3_8421544 (hcon #a #b))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMND α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEMND.sound frame_2_138 (hcon #a))

theorem ssubset_LogicEND : @LogicEND ℕ ⊂ LogicEMND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEND.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMD : @LogicEMD ℕ ⊂ LogicEMND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEMD.not_provable_axiomN⟩

theorem ssubset_LogicEMNP : @LogicEMNP ℕ ⊂ LogicEMND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomP_of_ND
  · obtain ⟨A, hA⟩ := LogicEMNP.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] →
      [F.IsSerial] → F ⊧ A) :
    A ∈ @LogicEMND α :=
  (supplementedBasicCanonicalModel LogicEMND).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMND).toFrame
      (supplementedBasicCanonicalModel LogicEMND).Val)

end LogicEMND

end
