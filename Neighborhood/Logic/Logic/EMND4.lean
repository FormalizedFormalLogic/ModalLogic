module

public import Neighborhood.Logic.Logic.EMND
public import Neighborhood.Logic.Logic.EMD4
public import Neighborhood.Logic.Logic.END4
public import Neighborhood.Logic.Logic.EMN4
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_8431784

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMND4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.ContainsUnit] [F.IsSerial] [F.IsTransitive] :
    A ∈ LogicEMND4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMND4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMND4.sound frame_1_2 hC⟩

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMND4 α) := by
  by_contra! hcon
  exact frame_3_8431784.not_valid_axiomC hab (LogicEMND4.sound frame_3_8431784 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMND4 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEMND4.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMND4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEMND4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMND4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEMND4.sound frame_2_138 (hcon #a))

theorem ssubset_LogicEMND : @LogicEMND ℕ ⊂ LogicEMND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMND.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMD4 : @LogicEMD4 ℕ ⊂ LogicEMND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEMD4.not_provable_axiomN⟩

theorem ssubset_LogicEND4 : @LogicEND4 ℕ ⊂ LogicEMND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEND4.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicEMN4 : @LogicEMN4 ℕ ⊂ LogicEMND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMN4.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, ProvableHilbert.axm (by grind), hA⟩

end LogicEMND4

end
