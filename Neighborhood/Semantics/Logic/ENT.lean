module

public import Neighborhood.Semantics.Logic.END
public import Neighborhood.Semantics.Logic.ET
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_8421512
public import Neighborhood.Semantics.Example.Frame3_8421544

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsReflexive] :
    A ∈ LogicENT → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp)

instance : (@LogicENT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENT.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.IsReflexive] → F ⊧ A) :
    A ∈ @LogicENT α :=
  (basicCanonicalModel LogicENT).mem_of_valid
    (h (basicCanonicalModel LogicENT).toFrame
      (basicCanonicalModel LogicENT).Val)

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicENT α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomB (LogicENT.sound frame_3_9471106 (hcon #a))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENT α) := by
  by_contra! hcon
  exact frame_3_8421544.not_valid_axiomC hab (LogicENT.sound frame_3_8421544 (hcon #a #b))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENT α) := by
  by_contra! hcon
  exact frame_3_8421512.not_valid_axiomFour
    (LogicENT.sound frame_3_8421512 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENT α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicENT.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENT α) := by
  by_contra! hcon
  exact frame_3_8421544.not_valid_axiomK hab (LogicENT.sound frame_3_8421544 (hcon #a #b))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENT α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicENT.sound frame_2_138 (hcon #a))

end LogicENT

theorem LogicET_ssubset_LogicENT : @LogicET ℕ ⊂ LogicENT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicET.not_provable_axiomN⟩

theorem LogicEND_ssubset_LogicENT : @LogicEND ℕ ⊂ LogicENT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (rfl | ⟨B, rfl⟩)
    · exact Logic.axiomN
    · exact Logic.axiomD
  · obtain ⟨A, hA⟩ := LogicEND.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end
