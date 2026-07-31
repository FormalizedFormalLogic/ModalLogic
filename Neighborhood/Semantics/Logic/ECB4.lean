module

public import Neighborhood.Semantics.Logic.ECN4
public import Neighborhood.Semantics.Logic.ECNB
public import Neighborhood.Semantics.Logic.EB4

/-!
# The neighborhood logic `LogicECB4`

Soundness and consistency of `LogicECB4`, the classical modal logic axiomatised by the
regularity axiom `C`, the symmetry axiom `B` and the transitivity axiom `Four`, with respect to
the neighborhood frames that are regular, symmetric and transitive. Also proves the strict
inclusions of `LogicECN4`, `LogicECNB` and `LogicEB4` in `LogicECB4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECB4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSymmetric] [F.IsTransitive] :
    A ∈ LogicECB4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECB4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECB4.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECB4 α) := by
  by_contra! hcon
  exact frame_3_9472136.not_valid_axiomM hab (LogicECB4.sound frame_3_9472136 (hcon #a #b))

lemma not_provable_axiomT {a : α} : ∃ A, Axioms.T A ∉ (@LogicECB4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicECB4.sound frame_1_3 (hcon #a))

end LogicECB4

theorem LogicECN4_ssubset_LogicECB4 : @LogicECN4 ℕ ⊂ LogicECB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomN
    · exact Logic.axiomFour
  · obtain ⟨A, hA⟩ := LogicECN4.not_provable_axiomB (a := (0 : ℕ))
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECNB_ssubset_LogicECB4 : @LogicECNB ℕ ⊂ LogicECB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomN
    · exact Logic.axiomB
  · obtain ⟨A, hA⟩ := LogicECNB.not_provable_axiomFour (a := (0 : ℕ))
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEB4_ssubset_LogicECB4 : @LogicEB4 ℕ ⊂ LogicECB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEB4.not_provable_axiomC (a := (0 : ℕ)) (b := 1) (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
