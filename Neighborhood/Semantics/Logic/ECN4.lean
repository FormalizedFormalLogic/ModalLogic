module

public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Logic.EC4
public import Neighborhood.Semantics.Logic.EN4

/-!
# The neighborhood logic `LogicECN4`

Soundness and consistency of `LogicECN4`, the classical modal logic axiomatised by `C`, `N := □⊤`
and the transitivity axiom `Four` over `LogicE`, with respect to regular neighborhood frames that
contain their unit and are transitive.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicECN4

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsRegular] [F.IsTransitive]
  : A ∈ LogicECN4 → F ⊧ A := Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicECN4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECN4.sound frame_1_2 hC⟩

omit [DecidableEq α] in
lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECN4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicECN4.sound frame_2_138 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicECN4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECN4.sound frame_1_3 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECN4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive
    (LogicECN4.sound frame_2_138 (hcon #a))

end LogicECN4

theorem LogicECN_ssubset_LogicECN4 : @LogicECN ℕ ⊂ LogicECN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicECN.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEC4_ssubset_LogicECN4 : @LogicEC4 ℕ ⊂ LogicECN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEC4.not_provable_axiomN⟩

theorem LogicEN4_ssubset_LogicECN4 : @LogicEN4 ℕ ⊂ LogicECN4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEN4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
