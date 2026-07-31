module

public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Logic.EP
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

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicENP α :=
  (basicCanonicalModel LogicENP).mem_of_valid
    (h (basicCanonicalModel LogicENP).toFrame
      (basicCanonicalModel LogicENP).Val)

omit [DecidableEq α] in
lemma not_provable_axiomD {a : α} : ∃ A, Axioms.D A ∉ (@LogicENP α) := by
  by_contra! hcon
  exact frame_2_238.not_valid_axiomD (LogicENP.sound frame_2_238 (hcon #a))

lemma not_provable_axiomM {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicENP α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicENP.sound frame_3_9471106 (hcon #a #b))

end LogicENP

theorem LogicEN_ssubset_LogicENP : @LogicEN ℕ ⊂ LogicENP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.P, (ProvableHilbert.axm (by grind)), LogicEN.not_provable_axiomP⟩

theorem LogicEP_ssubset_LogicENP : @LogicEP ℕ ⊂ LogicENP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEP.not_provable_axiomN⟩

end
