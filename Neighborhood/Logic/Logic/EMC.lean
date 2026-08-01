module

public import Neighborhood.Logic.Logic.EM
public import Neighborhood.Logic.Logic.EC
public import Neighborhood.Logic.Logic.EK
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_206

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMC

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] :
    A ∈ LogicEMC → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp)

instance : (@LogicEMC α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMC.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsRegular] → F ⊧ A) :
    A ∈ @LogicEMC α :=
  (supplementedBasicCanonicalModel LogicEMC).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMC).toFrame
      (supplementedBasicCanonicalModel LogicEMC).Val)

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMC α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMC.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMC α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour
    (LogicEMC.sound frame_2_8 (hcon #a))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMC α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMC.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMC α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMC.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMC α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMC.sound frame_1_0 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMC α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMC.sound frame_1_3 hcon)

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMC α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMC.sound frame_1_0 (hcon #a))

end LogicEMC

theorem LogicEMC.ssubset_LogicEC : @LogicEC ℕ ⊂ LogicEMC := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicEC.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
