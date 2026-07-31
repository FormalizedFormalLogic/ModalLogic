module

public import Neighborhood.Semantics.Logic.EMCND
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_140

/-!
# The neighborhood logic `LogicEMCNT`

Soundness and consistency of `LogicEMCNT`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the regularity axiom `C`, `N := □⊤` and the reflexivity axiom `T`, with
respect to the neighborhood frames that are monotonic, regular, contain their unit and are
reflexive.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCNT

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.ContainsUnit] [F.IsReflexive] :
    A ∈ LogicEMCNT → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCNT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCNT.sound frame_1_2 hC⟩

end LogicEMCNT

theorem LogicEMCND_ssubset_LogicEMCNT : @LogicEMCND ℕ ⊂ LogicEMCNT := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD
  · intro h
    have hT : Axioms.T #0 ∈ (@LogicEMCND ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomT (LogicEMCND.sound frame_2_140 hT)

end
