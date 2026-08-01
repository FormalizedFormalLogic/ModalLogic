module

public import Neighborhood.Logic.Logic.EMT
public import Neighborhood.Logic.Logic.ENT
public import Neighborhood.Logic.Logic.EMND
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_8421512
public import Neighborhood.Semantics.Example.Frame3_8421544

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMNT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.ContainsUnit]
    [F.IsReflexive] :
    A ∈ LogicEMNT → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMNT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMNT.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMNT α) := by
  by_contra! hcon
  exact frame_3_8421544.not_valid_axiomK hab (LogicEMNT.sound frame_3_8421544 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMNT α) := by
  by_contra! hcon
  exact frame_3_8421544.not_valid_axiomC hab (LogicEMNT.sound frame_3_8421544 (hcon #a #b))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMNT α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEMNT.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMNT α) := by
  by_contra! hcon
  exact frame_3_8421512.not_valid_axiomFour (LogicEMNT.sound frame_3_8421512 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMNT α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEMNT.sound frame_2_138 (hcon #a))

end LogicEMNT

theorem LogicEMNT.ssubset_LogicEMT : @LogicEMT ℕ ⊂ LogicEMNT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms
      (fun x hx => hx.elim
        (fun h => Or.inl (Or.inl h))
        (fun h => Or.inr h))
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEMT.not_provable_axiomN⟩

theorem LogicEMNT.ssubset_LogicENT : @LogicENT ℕ ⊂ LogicEMNT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicENT.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMNT.ssubset_LogicEMND : @LogicEMND ℕ ⊂ LogicEMNT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomD
  · obtain ⟨A, hA⟩ := LogicEMND.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end
