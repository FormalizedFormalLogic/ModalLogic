module

public import Neighborhood.Semantics.Logic.ENT
public import Neighborhood.Semantics.Example.Frame1_2
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

end
