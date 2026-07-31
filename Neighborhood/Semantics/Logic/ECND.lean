module

public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Logic.ECP
public import Neighborhood.Semantics.Logic.END

/-!
# The neighborhood logic `LogicECND`

Soundness and consistency of `LogicECND`, the classical modal logic axiomatised by the regularity
axiom `C`, `N := □⊤`, and the seriality axiom `D`, with respect to the regular, unit-containing,
and serial neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECND

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.ContainsUnit]
    [F.IsSerial] :
    A ∈ LogicECND → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECND α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECND.sound frame_1_2 hC⟩

lemma not_provable_axiomB {a : α} : ∃ A, Axioms.B A ∉ (@LogicECND α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicECND.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFive {a : α} : ∃ A, Axioms.Five A ∉ (@LogicECND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicECND.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFour {a : α} : ∃ A, Axioms.Four A ∉ (@LogicECND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicECND.sound frame_2_140 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECND α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicECND.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomT {a : α} : ∃ A, Axioms.T A ∉ (@LogicECND α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicECND.sound frame_2_170 (hcon #a))

end LogicECND

theorem LogicECN_ssubset_LogicECND : @LogicECN ℕ ⊂ LogicECND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicECN.not_provable_axiomD (a := (0 : ℕ))
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECP_ssubset_LogicECND : @LogicECP ℕ ⊂ LogicECND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, C, rfl⟩ | rfl)
    · exact Logic.axiomC
    · exact Logic.axiomP_of_ND
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicECP.not_provable_axiomN⟩

theorem LogicEND_ssubset_LogicECND : @LogicEND ℕ ⊂ LogicECND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEND.not_provable_axiomC (a := (0 : ℕ)) (b := 1) (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
