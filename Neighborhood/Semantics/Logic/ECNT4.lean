module

public import Neighborhood.Semantics.Logic.ENT4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame3_10520744

/-!
# The neighborhood logic `LogicECNT4`

Soundness and consistency of `LogicECNT4`, the classical modal logic axiomatised by the regularity
axiom `C`, the unit axiom `N := □⊤`, the reflexivity axiom `T`, and the transitivity axiom `Four`,
with respect to the regular, unit-containing, reflexive, and transitive neighborhood frames.
-/

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

end LogicECNT4

theorem LogicENT4_ssubset_LogicECNT4 : @LogicENT4 ℕ ⊂ LogicECNT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicENT4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_10520744.not_valid_axiomC (LogicENT4.sound frame_3_10520744 hC)

end
