module

public import Neighborhood.Semantics.Logic.EMCD45
public import Neighborhood.Semantics.Logic.EMCNT4
public import Neighborhood.Semantics.Logic.EMB4
public import Neighborhood.Semantics.Logic.EMTB
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame3_8437920

/-!
# The neighborhood logic `LogicEMT5`

Soundness and consistency of `LogicEMT5`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the reflexivity axiom `T` and the euclideanness axiom `Five`, with
respect to the neighborhood frames that are monotonic, reflexive and euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMT5.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsReflexive]
    [F.IsEuclidean] :
    A ∈ LogicEMT5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMT5.consistent : (@LogicEMT5 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMT5.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMT5 α)) :=
  MaximalConsistentSet.nonempty LogicEMT5.consistent

theorem LogicEMCD45_ssubset_LogicEMT5 : @LogicEMCD45 ℕ ⊂ LogicEMT5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomD |
        exact Logic.axiomFour | exact Logic.axiomFive
  · intro h
    have hT : Axioms.T #0 ∈ (@LogicEMCD45 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomT (LogicEMCD45.sound frame_2_170 hT)

theorem LogicEMCNT4_ssubset_LogicEMT5 : @LogicEMCNT4 ℕ ⊂ LogicEMT5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT |
        exact Logic.axiomFour
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEMCNT4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomFive (LogicEMCNT4.sound frame_2_138 hFive)

theorem LogicEMB4_ssubset_LogicEMT5 : @LogicEMB4 ℕ ⊂ LogicEMT5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomB | exact Logic.axiomFour
  · intro h
    have hT : Axioms.T #0 ∈ (@LogicEMB4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomT (LogicEMB4.sound frame_1_3 hT)

theorem LogicEMTB_ssubset_LogicEMT5 : @LogicEMTB ℕ ⊂ LogicEMT5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomT | exact Logic.axiomB
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEMTB ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_8437920.not_valid_axiomFive (LogicEMTB.sound frame_3_8437920 hFive)

end
