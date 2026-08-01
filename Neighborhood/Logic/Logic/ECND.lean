module

public import Neighborhood.Logic.Logic.ECN
public import Neighborhood.Logic.Logic.ECP
public import Neighborhood.Logic.Logic.END
public import Neighborhood.Semantics.Example.Frame3_8553090

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

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECND α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicECND.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicECND.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicECND.sound frame_2_140 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECND α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicECND.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicECND α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicECND.sound frame_2_170 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECND α) := by
  by_contra! hcon
  exact frame_3_8553090.not_valid_axiomK hab (LogicECND.sound frame_3_8553090 (hcon #a #b))

theorem ssubset_LogicECN : @LogicECN ℕ ⊂ LogicECND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicECN.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECP : @LogicECP ℕ ⊂ LogicECND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicECP.not_provable_axiomN⟩

theorem ssubset_LogicEND : @LogicEND ℕ ⊂ LogicECND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEND.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

/-- Over `ECN`, the axiom `P` and the axiom scheme `D` axiomatise the same logic. -/
theorem eq_LogicECNP : (@LogicECND α) = LogicECNP := by
  hilbert_eq_axioms

end LogicECND

end
