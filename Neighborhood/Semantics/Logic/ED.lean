module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Example.Frame3_10528928
public import Neighborhood.Semantics.Example.Frame2_53

/-!
# The neighborhood logic `LogicED`

Soundness and consistency of `LogicED`, the classical modal logic axiomatised by the seriality
axiom `D`, with respect to the serial neighborhood frames (`Frame.IsSerial`), and the strict
inclusion of `LogicE` in `LogicED`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicED

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] :
    A ∈ LogicED → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, rfl⟩; simp)

instance : (@LogicED α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicED.sound frame_1_2 hC⟩

lemma not_provable_axiomB {a : α} : ∃ A, Axioms.B A ∉ (@LogicED α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB
    (LogicED.sound frame_1_0 (hcon #a))

lemma not_provable_axiomC [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicED α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomC hab (LogicED.sound frame_3_10528928 (hcon #a #b))

lemma not_provable_axiomFive {a : α} : ∃ A, Axioms.Five A ∉ (@LogicED α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive
    (LogicED.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour {a : α} : ∃ A, Axioms.Four A ∉ (@LogicED α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour
    (LogicED.sound frame_1_1 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicED α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomM hab (LogicED.sound frame_1_1 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicED α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicED.sound frame_1_0 hcon)

lemma not_provable_axiomT {a : α} : ∃ A, Axioms.T A ∉ (@LogicED α) := by
  by_contra! hcon
  exact frame_1_1.not_isReflexive (isReflexive_of_valid_axiomT (LogicED.sound frame_1_1 (hcon #a)))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicED α) := by
  intro hcon
  simpa using (notContainsEmpty_of_valid_axiomP (LogicED.sound frame_2_53 hcon)).not_contains_empty
    (x := 0)

end LogicED

theorem LogicE_ssubset_LogicED : @LogicE ℕ ⊂ LogicED := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · obtain ⟨A, hA⟩ := LogicE.not_provable_axiomD (a := (0 : ℕ))
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
