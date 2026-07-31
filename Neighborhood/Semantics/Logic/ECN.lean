module

public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Example.Frame2_153

/-!
# The neighborhood logic `LogicECN`

Soundness, consistency and completeness of `LogicECN`, the classical modal logic axiomatised by
both the regularity axiom `C` and `N := □⊤` over `LogicE`, with respect to the regular
neighborhood frames containing their unit.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECN

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] :
    A ∈ LogicECN → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

instance : (@LogicECN α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECN.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsRegular] → [F.ContainsUnit] → F ⊧ A) :
    A ∈ @LogicECN α :=
  (basicCanonicalModel LogicECN).mem_of_valid
    (h (basicCanonicalModel LogicECN).toFrame
      (basicCanonicalModel LogicECN).Val)

omit [DecidableEq α] in
lemma not_provable_axiomB {a : α} : ∃ A, Axioms.B A ∉ (@LogicECN α) := by
  by_contra! hcon
  exact frame_2_137.not_valid_axiomB
    (LogicECN.sound frame_2_137 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomD {a : α} : ∃ A, Axioms.D A ∉ (@LogicECN α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicECN.sound frame_1_3 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFive {a : α} : ∃ A, Axioms.Five A ∉ (@LogicECN α) := by
  by_contra! hcon
  exact frame_2_137.not_valid_axiomFive
    (LogicECN.sound frame_2_137 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFour {a : α} : ∃ A, Axioms.Four A ∉ (@LogicECN α) := by
  by_contra! hcon
  exact frame_2_137.not_valid_axiomFour
    (LogicECN.sound frame_2_137 (hcon #a))

lemma not_provable_axiomM {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECN α) := by
  by_contra! hcon
  exact frame_2_153.not_valid_axiomM hab
    (LogicECN.sound frame_2_153 (hcon #a #b))

end LogicECN

theorem LogicEC_ssubset_LogicECN : @LogicEC ℕ ⊂ LogicECN := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEC.not_provable_axiomN⟩

theorem LogicEN_ssubset_LogicECN : @LogicEN ℕ ⊂ LogicECN := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicEN.not_provable_axiomC (a := (0 : ℕ)) (b := 1) (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
