module

public import Neighborhood.Semantics.Logic.EN5
public import Neighborhood.Semantics.Logic.EMN

/-!
# The neighborhood logic `LogicEM5`

Soundness and consistency of `LogicEM5`, the classical modal logic axiomatised by the
monotonicity axiom `M` and the euclideanness axiom `Five`, with respect to the neighborhood
frames that are monotonic and euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEM5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsEuclidean] :
    A ∈ LogicEM5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEM5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEM5.sound frame_1_2 hC⟩

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEM5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomC hab (LogicEM5.sound frame_3_10528928 (hcon #a #b))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEM5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEM5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEM5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomFour (LogicEM5.sound frame_3_10528928 (hcon #a))

end LogicEM5

theorem LogicEN5_ssubset_LogicEM5 : @LogicEN5 ℕ ⊂ LogicEM5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (rfl | ⟨_, rfl⟩) <;> first | exact Logic.axiomN | exact Logic.axiomFive
  · obtain ⟨A, B, hA⟩ := LogicEN5.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMN_ssubset_LogicEM5 : @LogicEMN ℕ ⊂ LogicEM5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (⟨_, _, rfl⟩ | rfl) <;> first | exact Logic.axiomM | exact Logic.axiomN
  · obtain ⟨A, hA⟩ := LogicEMN.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

end
