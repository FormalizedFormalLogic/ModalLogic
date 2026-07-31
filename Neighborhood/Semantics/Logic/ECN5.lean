module

public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Logic.EC5
public import Neighborhood.Semantics.Logic.EN5
public import Neighborhood.Semantics.Example.Frame3_9472136

/-!
# The neighborhood logic `LogicECN5`

Soundness and consistency of `LogicECN5`, the classical modal logic axiomatised by `C`, `N := □⊤`
and the Euclideanness axiom `Five` over `LogicE`, with respect to regular neighborhood frames that
contain their unit and are Euclidean.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicECN5

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsRegular] [F.IsEuclidean]
  : A ∈ LogicECN5 → F ⊧ A := Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicECN5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECN5.sound frame_1_2 hC⟩

omit [DecidableEq α] in
lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECN5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECN5.sound frame_1_3 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECN5 α) := by
  by_contra! hcon
  exact frame_2_186.not_valid_axiomFour
    (LogicECN5.sound frame_2_186 (hcon #a))

lemma not_provable_axiomM (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECN5 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicECN5.sound frame_3_9472136 (hcon #a #b))

end LogicECN5

theorem LogicECN_ssubset_LogicECN5 : @LogicECN ℕ ⊂ LogicECN5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicECN.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEC5_ssubset_LogicECN5 : @LogicEC5 ℕ ⊂ LogicECN5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEC5.not_provable_axiomN⟩

theorem LogicEN5_ssubset_LogicECN5 : @LogicEN5 ℕ ⊂ LogicECN5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEN5.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
