module

public import Neighborhood.Semantics.Logic.EMCD45
public import Neighborhood.Semantics.Logic.EMCNT4
public import Neighborhood.Semantics.Logic.EMB4
public import Neighborhood.Semantics.Logic.EMTB
public import Neighborhood.Semantics.Logic.ECT5
public import Neighborhood.Logic.Equiv.EMT5_EMCNT5

/-!
# The neighborhood logic `LogicEMT5`

Soundness and consistency of `LogicEMT5`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the reflexivity axiom `T` and the euclideanness axiom `Five`, with
respect to the neighborhood frames that are monotonic, reflexive and euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMT5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsReflexive]
    [F.IsEuclidean] :
    A ∈ LogicEMT5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMT5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMT5.sound frame_1_2 hC⟩

end LogicEMT5

theorem LogicEMCD45_ssubset_LogicEMT5 : @LogicEMCD45 ℕ ⊂ LogicEMT5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomD |
        exact Logic.axiomFour | exact Logic.axiomFive
  · obtain ⟨A, hA⟩ := LogicEMCD45.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMCNT4_ssubset_LogicEMT5 : @LogicEMCNT4 ℕ ⊂ LogicEMT5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT |
        exact Logic.axiomFour
  · obtain ⟨A, hA⟩ := LogicEMCNT4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMB4_ssubset_LogicEMT5 : @LogicEMB4 ℕ ⊂ LogicEMT5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomB | exact Logic.axiomFour
  · obtain ⟨A, hA⟩ := LogicEMB4.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMTB_ssubset_LogicEMT5 : @LogicEMTB ℕ ⊂ LogicEMT5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomT | exact Logic.axiomB
  · obtain ⟨A, hA⟩ := LogicEMTB.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECT5_ssubset_LogicEMT5 : @LogicECT5 ℕ ⊂ LogicEMT5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · rw [LogicEMT5_eq_LogicEMCT5]
    exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicECT5.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
