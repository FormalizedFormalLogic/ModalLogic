module

public import Neighborhood.Semantics.Logic.EMCND4
public import Neighborhood.Semantics.Logic.EMCNT
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_8421512

/-!
# The neighborhood logic `LogicEMCNT4`

Soundness and consistency of `LogicEMCNT4`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the regularity axiom `C`, `N := □⊤`, the reflexivity axiom `T` and the
transitivity axiom `Four`, with respect to the neighborhood frames that are monotonic, regular,
contain their unit, reflexive and transitive.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCNT4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.ContainsUnit] [F.IsReflexive] [F.IsTransitive] :
    A ∈ LogicEMCNT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCNT4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCNT4.sound frame_1_2 hC⟩

end LogicEMCNT4

theorem LogicEMCND4_ssubset_LogicEMCNT4 : @LogicEMCND4 ℕ ⊂ LogicEMCNT4 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD |
        exact Logic.axiomFour
  · intro h
    have hT : Axioms.T #0 ∈ (@LogicEMCND4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomT (LogicEMCND4.sound frame_2_170 hT)

theorem LogicEMCNT_ssubset_LogicEMCNT4 : @LogicEMCNT ℕ ⊂ LogicEMCNT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicEMCNT ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_8421512.not_valid_axiomFour (LogicEMCNT.sound frame_3_8421512 hFour)

end
