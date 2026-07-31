module

public import Neighborhood.Semantics.Logic.EMT4
public import Neighborhood.Semantics.Logic.EMC4

/-!
# The neighborhood logic `LogicEMCT4`

Soundness and consistency of `LogicEMCT4`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C`, the reflexivity axiom `T`, and
the transitivity axiom `Four`, with respect to the neighborhood frames that are monotonic,
regular, reflexive, and transitive.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCT4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsReflexive] [F.IsTransitive] :
    A ∈ LogicEMCT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCT4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCT4.sound frame_1_2 hC⟩

end LogicEMCT4

theorem LogicEMT4_ssubset_LogicEMCT4 : @LogicEMT4 ℕ ⊂ LogicEMCT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEMT4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
