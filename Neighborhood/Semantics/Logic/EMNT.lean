module

public import Neighborhood.Semantics.Logic.EMT
public import Neighborhood.Semantics.Logic.ENT
public import Neighborhood.Semantics.Logic.EMND

/-!
# The neighborhood logic `LogicEMNT`

Soundness and consistency of `LogicEMNT`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the unit axiom `N`, and the reflexivity axiom `T`, with respect to
the monotonic, unit-containing, and reflexive neighborhood frames.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicEMNT

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.ContainsUnit]
    [F.IsReflexive] :
    A ∈ LogicEMNT → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicEMNT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMNT.sound frame_1_2 hC⟩

end LogicEMNT

theorem LogicEMT_ssubset_LogicEMNT : @LogicEMT ℕ ⊂ LogicEMNT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms
      (fun x hx => hx.elim
        (fun h => Or.inl (Or.inl h))
        (fun h => Or.inr h))
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEMT.not_provable_axiomN⟩

theorem LogicENT_ssubset_LogicEMNT : @LogicENT ℕ ⊂ LogicEMNT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicENT.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMND_ssubset_LogicEMNT : @LogicEMND ℕ ⊂ LogicEMNT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomD
  · obtain ⟨A, hA⟩ := LogicEMND.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end
