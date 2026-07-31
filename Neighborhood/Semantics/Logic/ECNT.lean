module

public import Neighborhood.Semantics.Logic.ECND
public import Neighborhood.Semantics.Logic.ECT
public import Neighborhood.Semantics.Logic.ENT
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_8421544

/-!
# The neighborhood logic `LogicECNT`

Soundness and consistency of `LogicECNT`, the classical modal logic axiomatised by the regularity
axiom `C`, the unit axiom `N := □⊤`, and the reflexivity axiom `T`, with respect to the regular,
unit-containing, and reflexive neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicECNT.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.ContainsUnit]
    [F.IsReflexive] :
    A ∈ LogicECNT → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

theorem LogicECNT.consistent : (@LogicECNT α).IsConsistent := by
  by_contra! hC
  simpa using LogicECNT.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECNT α)) :=
  MaximalConsistentSet.nonempty LogicECNT.consistent

theorem LogicENT_ssubset_LogicECNT : @LogicENT ℕ ⊂ LogicECNT := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicENT ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_8421544.not_valid_axiomC (LogicENT.sound frame_3_8421544 hC)

theorem LogicECT_ssubset_LogicECNT : @LogicECT ℕ ⊂ LogicECNT := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicECT ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicECT.sound frame_1_0 hN)

theorem LogicECND_ssubset_LogicECNT : @LogicECND ℕ ⊂ LogicECNT := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomN
    · exact Logic.axiomD
  · intro h
    have hT : Axioms.T #0 ∈ @LogicECND ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomT (LogicECND.sound frame_2_170 hT)

end
