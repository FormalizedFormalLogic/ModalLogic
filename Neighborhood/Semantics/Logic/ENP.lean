module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Logic.EP
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3

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

end LogicENP

theorem LogicEN_ssubset_LogicENP : @LogicEN ℕ ⊂ LogicENP := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hP : (Axioms.P : Formula ℕ) ∈ @LogicEN ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomP (LogicEN.sound frame_1_3 hP)

theorem LogicEP_ssubset_LogicENP : @LogicEP ℕ ⊂ LogicENP := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEP ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicEP.sound frame_1_0 hN)

end
