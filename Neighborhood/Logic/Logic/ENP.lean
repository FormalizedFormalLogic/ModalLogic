module

public import Neighborhood.Logic.Logic.EN
public import Neighborhood.Logic.Logic.EP
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame2_206
public import Neighborhood.Semantics.Example.Frame2_238

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicENP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.NotContainsEmpty] :
    A ∈ LogicENP → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | rfl) <;> simp)

instance : (@LogicENP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicENP.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicENP α :=
  (basicCanonicalModel LogicENP).mem_of_valid
    (h (basicCanonicalModel LogicENP).toFrame
      (basicCanonicalModel LogicENP).Val)

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicENP α) := by
  by_contra! hcon
  exact frame_2_238.not_valid_axiomD (LogicENP.sound frame_2_238 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENP α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicENP.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicENP α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicENP.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicENP α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicENP.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicENP α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicENP.sound frame_2_140 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicENP α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicENP.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicENP α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicENP.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicENP α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicENP.sound frame_2_138 (hcon #a))

theorem ssubset_LogicEN : @LogicEN ℕ ⊂ LogicENP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · exact ⟨Axioms.P, (ProvableHilbert.axm (by grind)), LogicEN.not_provable_axiomP⟩

theorem ssubset_LogicEP : @LogicEP ℕ ⊂ LogicENP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEP.not_provable_axiomN⟩

end LogicENP

end
