module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame2_78
public import Neighborhood.Semantics.Example.Frame2_206

/-!
# The neighborhood logic `LogicEP`

Soundness and consistency of `LogicEP`, the classical modal logic axiomatised by the
possibility axiom `P := ∼□⊥`, with respect to the neighborhood frames in which no world has the
empty set as one of its neighborhoods (`Frame.NotContainsEmpty`). Also that `D` is not among its
theorems.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.NotContainsEmpty] :
    A ∈ LogicEP → F ⊧ A :=
  Hilbert.sound (by rintro _ rfl; simp)

instance : (@LogicEP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEP.sound frame_1_2 hC⟩

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEP α) := by
  by_contra! hcon
  exact frame_2_78.not_valid_axiomC hab (LogicEP.sound frame_2_78 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEP α) := by
  by_contra! hcon
  exact frame_2_78.not_valid_axiomM hab (LogicEP.sound frame_2_78 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEP α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEP.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEP α) := by
  by_contra! hcon
  exact frame_2_78.not_valid_axiomT (LogicEP.sound frame_2_78 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEP α) := by
  by_contra! hcon
  exact frame_2_78.not_isSerial (isSerial_of_valid_axiomD (LogicEP.sound frame_2_78 (hcon #a)))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEP α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicEP.sound _ (hcon #a #b))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEP.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEP α) := by
  by_contra! hcon
  exact frame_2_8.not_valid_axiomFour (LogicEP.sound frame_2_8 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEP α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEP.sound frame_1_0 (hcon #a))

end LogicEP

theorem LogicE_ssubset_LogicEP : @LogicE ℕ ⊂ LogicEP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · exact ⟨Axioms.P, (ProvableHilbert.axm (by grind)), LogicE.not_provable_axiomP⟩

end
