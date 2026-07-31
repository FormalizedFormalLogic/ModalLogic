module

public import Neighborhood.Semantics.Logic.ENT4

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
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicENT4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
