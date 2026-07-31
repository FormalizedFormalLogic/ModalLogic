module

public import Neighborhood.Semantics.Logic.EMT
public import Neighborhood.Semantics.Logic.ENT
public import Neighborhood.Semantics.Logic.EMND
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_9471106

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
theorem consistent : (@LogicEMNT α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMNT.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMNT α)) :=
  MaximalConsistentSet.nonempty LogicEMNT.consistent

end LogicEMNT

theorem LogicEMT_ssubset_LogicEMNT : @LogicEMT ℕ ⊂ LogicEMNT := by
  constructor
  · exact Hilbert.subset_of_subset_axioms
      (fun x hx => hx.elim
        (fun h => Or.inl (Or.inl h))
        (fun h => Or.inr h))
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ (@LogicEMT ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicEMT.sound frame_1_0 hN)

theorem LogicENT_ssubset_LogicEMNT : @LogicENT ℕ ⊂ LogicEMNT := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicENT ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_9471106.not_valid_axiomM (LogicENT.sound frame_3_9471106 hM)

theorem LogicEMND_ssubset_LogicEMNT : @LogicEMND ℕ ⊂ LogicEMNT := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomD
  · intro h
    have hT : Axioms.T #0 ∈ @LogicEMND ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomT (LogicEMND.sound frame_2_170 hT)

end
