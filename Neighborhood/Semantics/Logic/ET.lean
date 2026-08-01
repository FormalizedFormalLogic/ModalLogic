module

public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.EP
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_72
public import Neighborhood.Semantics.Example.Frame3_130
public import Neighborhood.Semantics.Example.Frame3_168

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicET

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsReflexive] :
    A ∈ LogicET → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, rfl⟩; simp)

instance : (@LogicET α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicET.sound frame_1_2 hC⟩

theorem complete [DecidableEq α] (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsReflexive] → F ⊧ A) :
    A ∈ @LogicET α :=
  (basicCanonicalModel LogicET).mem_of_valid
    (h (basicCanonicalModel LogicET).toFrame
      (basicCanonicalModel LogicET).Val)

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicET α) := by
  by_contra! hcon
  exact frame_3_168.not_valid_axiomC hab (LogicET.sound frame_3_168 (hcon #a #b))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicET α) := by
  by_contra! hcon
  exact frame_2_72.not_isTransitive (isTransitive_of_valid_axiomFour (LogicET.sound frame_2_72 (hcon #a)))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicET α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicET.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicET α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicET.sound frame_1_0 hcon)

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicET α) := by
  by_contra! hcon
  exact frame_3_130.not_valid_axiomK hab (LogicET.sound _ (hcon #a #b))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicET α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicET.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicET α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicET.sound frame_1_0 (hcon #a))

end LogicET

theorem LogicED_ssubset_LogicET : @LogicED ℕ ⊂ LogicET := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ⟨A, rfl⟩
    exact Logic.C_trans Logic.axiomT Logic.diaTc
  · obtain ⟨A, hA⟩ := LogicED.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEP_ssubset_LogicET : @LogicEP ℕ ⊂ LogicET := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ rfl
    exact Logic.axiomP
  · obtain ⟨A, hA⟩ := LogicEP.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (Logic.HasAxiomT.T _), hA⟩

end
