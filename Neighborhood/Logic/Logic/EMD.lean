module

public import Neighborhood.Logic.Logic.ED
public import Neighborhood.Logic.Logic.EMP
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame2_172
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame3_10528928

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMD

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSerial] :
    A ∈ LogicEMD → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMD α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMD.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsSerial] → F ⊧ A) :
    A ∈ @LogicEMD α :=
  (supplementedBasicCanonicalModel LogicEMD).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMD).toFrame
      (supplementedBasicCanonicalModel LogicEMD).Val)

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMD α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomC hab (LogicEMD.sound frame_3_10528928 (hcon #a #b))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMD α) := by
  by_contra! hcon
  exact frame_2_172.not_valid_axiomFour (LogicEMD.sound frame_2_172 (hcon #a))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMD α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMD.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMD α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEMD.sound frame_2_170 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMD α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomK hab (LogicEMD.sound frame_3_10528928 (hcon #a #b))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMD.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMD.sound frame_1_0 (hcon #a))

end LogicEMD

theorem LogicEMD.ssubset_LogicED : @LogicED ℕ ⊂ LogicEMD := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicED.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMD.ssubset_LogicEMP : @LogicEMP ℕ ⊂ LogicEMD := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, C, rfl⟩ | rfl) <;> first | exact Logic.axiomM | exact Logic.axiomP_of_MD
  · obtain ⟨A, hA⟩ := LogicEMP.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
