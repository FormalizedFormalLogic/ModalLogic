module

public import Neighborhood.Semantics.Logic.EMCN
public import Neighborhood.Semantics.Logic.EM5
public import Neighborhood.Semantics.Logic.ECN5
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_9472136
public import Neighborhood.Semantics.Example.Frame3_10528928

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

theorem LogicEM5_ssubset_LogicEMC5 : @LogicEM5 ℕ ⊂ LogicEMC5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ (@LogicEM5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_10528928.not_valid_axiomC (LogicEM5.sound frame_3_10528928 hC)

theorem LogicECN5_ssubset_LogicEMC5 : @LogicECN5 ℕ ⊂ LogicEMC5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomN
    · exact Logic.axiomFive
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicECN5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_9472136.not_valid_axiomM (LogicECN5.sound frame_3_9472136 hM)

end
