module

public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_75

/-!
# The neighborhood logic `LogicEC4`

Soundness and consistency of `LogicEC4`, the classical
modal logic axiomatised by the regularity axiom `C` and the transitivity axiom `Four` over
`LogicE`, with respect to the regular and transitive neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEC4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsTransitive] :
    A ∈ LogicEC4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEC4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEC4.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEC4 α) := by
  by_contra! hcon
  exact frame_2_75.not_valid_axiomK hab (LogicEC4.sound frame_2_75 (hcon #a #b))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEC4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEC4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEC4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEC4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicEC4 α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicEC4.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEC4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEC4.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEC4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEC4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEC4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEC4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEC4 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEC4.sound frame_1_3 hcon)

end LogicEC4

theorem LogicEC_ssubset_LogicEC4 : (@LogicEC ℕ) ⊂ LogicEC4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEC.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicE4_ssubset_LogicEC4 : @LogicE4 ℕ ⊂ LogicEC4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicE4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
