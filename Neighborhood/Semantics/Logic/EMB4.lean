module

public import Neighborhood.Semantics.Logic.EMB
public import Neighborhood.Semantics.Logic.EMC45
public import Neighborhood.Semantics.Logic.ECB4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_9472136

/-!
# The neighborhood logic `LogicEMB4`

Soundness and consistency of `LogicEMB4`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the symmetry axiom `B` and the transitivity axiom `Four`, with respect to
the neighborhood frames that are monotonic, symmetric and transitive.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMB4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSymmetric]
    [F.IsTransitive] :
    A ∈ LogicEMB4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMB4.consistent : (@LogicEMB4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMB4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMB4 α)) :=
  MaximalConsistentSet.nonempty LogicEMB4.consistent

theorem LogicEMB_ssubset_LogicEMB4 : @LogicEMB ℕ ⊂ LogicEMB4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicEMB ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomFour (LogicEMB.sound frame_2_140 hFour)

theorem LogicEMC45_ssubset_LogicEMB4 : @LogicEMC45 ℕ ⊂ LogicEMB4 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomFour |
        exact Logic.axiomFive
  · intro h
    have hB : Axioms.B #0 ∈ (@LogicEMC45 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomB (LogicEMC45.sound frame_2_170 hB)

theorem LogicECB4_ssubset_LogicEMB4 : @LogicECB4 ℕ ⊂ LogicEMB4 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomB
    · exact Logic.axiomFour
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicECB4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_9472136.not_valid_axiomM (LogicECB4.sound frame_3_9472136 hM)

end
