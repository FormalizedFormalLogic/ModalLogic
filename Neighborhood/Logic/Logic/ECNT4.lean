module

public import Neighborhood.Logic.Logic.ENT4
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_9471106

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECNT4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.ContainsUnit]
    [F.IsReflexive] [F.IsTransitive] :
    A ∈ LogicECNT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECNT4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECNT4.sound frame_1_2 hC⟩

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECNT4 α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicECNT4.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicECNT4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicECNT4.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicECNT4 α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicECNT4.sound frame_2_138 (hcon #a))

theorem ssubset_LogicENT4 : @LogicENT4 ℕ ⊂ LogicECNT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicENT4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end LogicECNT4

end
