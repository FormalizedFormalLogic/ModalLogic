module

public import Neighborhood.Semantics.Logic.ECD
public import Neighborhood.Semantics.Logic.EC5
public import Neighborhood.Semantics.Logic.ED5
public import Neighborhood.Semantics.Example.Frame2_90
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_8553090
public import Neighborhood.Semantics.Example.Frame3_10529440

/-!
# The neighborhood logic `LogicECD5`

Soundness and consistency of `LogicECD5`, the classical modal logic axiomatised by the regularity
axiom `C`, the seriality axiom `D`, and the euclideanity axiom `5`, with respect to the regular,
serial, and euclidean neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECD5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial]
    [F.IsEuclidean] :
    A ∈ LogicECD5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECD5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECD5.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECD5 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomK hab (LogicECD5.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECD5 α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomM hab (LogicECD5.sound frame_3_8553090 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECD5 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomN (LogicECD5.sound frame_2_90 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECD5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicECD5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECD5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicECD5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECD5 α) := by
  intro hcon
  exact frame_2_90.not_valid_axiomP (LogicECD5.sound frame_2_90 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECD5 α) := by
  by_contra! hcon
  exact frame_3_10529440.not_valid_axiomFour (LogicECD5.sound frame_3_10529440 (hcon #a))

end LogicECD5

theorem LogicECD_ssubset_LogicECD5 : @LogicECD ℕ ⊂ LogicECD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECD.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEC5_ssubset_LogicECD5 : @LogicEC5 ℕ ⊂ LogicECD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEC5.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicED5_ssubset_LogicECD5 : @LogicED5 ℕ ⊂ LogicECD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicED5.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
