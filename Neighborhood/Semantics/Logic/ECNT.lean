module

public import Neighborhood.Semantics.Logic.ECND
public import Neighborhood.Semantics.Logic.ECT
public import Neighborhood.Semantics.Logic.ENT
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_8421512
public import Neighborhood.Semantics.Example.Frame3_9471106

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECNT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.ContainsUnit]
    [F.IsReflexive] :
    A ∈ LogicECNT → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECNT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECNT.sound frame_1_2 hC⟩

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECNT α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicECNT.sound frame_2_138 (hcon #a))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicECNT α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomK hab (LogicECNT.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECNT α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicECNT.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicECNT α) := by
  by_contra! hcon
  exact frame_3_8421512.not_valid_axiomFour (LogicECNT.sound frame_3_8421512 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECNT α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicECNT.sound frame_2_138 (hcon #a))

end LogicECNT

theorem LogicENT_ssubset_LogicECNT : @LogicENT ℕ ⊂ LogicECNT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicENT.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECT_ssubset_LogicECNT : @LogicECT ℕ ⊂ LogicECNT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicECT.not_provable_axiomN⟩

theorem LogicECND_ssubset_LogicECNT : @LogicECND ℕ ⊂ LogicECNT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomN
    · exact Logic.axiomD
  · obtain ⟨A, hA⟩ := LogicECND.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end
