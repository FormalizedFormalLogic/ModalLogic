module

public import Neighborhood.Semantics.Logic.EMCN
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_140

/-!
# The neighborhood logic `LogicEMC5`

Soundness and consistency of `LogicEMC5`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the regularity axiom `C` and the euclideanness axiom `Five`, with respect
to the neighborhood frames that are monotonic, regular and euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMC5.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsEuclidean] :
    A ∈ LogicEMC5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMC5.consistent : (@LogicEMC5 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMC5.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMC5 α)) :=
  MaximalConsistentSet.nonempty LogicEMC5.consistent

theorem LogicEMCN_ssubset_LogicEMC5 : @LogicEMCN ℕ ⊂ LogicEMC5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEMCN ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomFive (LogicEMCN.sound frame_2_140 hFive)

end
