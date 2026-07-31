module

public import Neighborhood.Semantics.Logic.EMB
public import Neighborhood.Semantics.Logic.EMC45
public import Neighborhood.Semantics.Logic.ECB4

/-!
# The neighborhood logic `LogicEMB4`

Soundness and consistency of `LogicEMB4`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the symmetry axiom `B` and the transitivity axiom `Four`, with respect to
the neighborhood frames that are monotonic, symmetric and transitive.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMB4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSymmetric]
    [F.IsTransitive] :
    A ∈ LogicEMB4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMB4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMB4.sound frame_1_2 hC⟩

lemma not_provable_axiomT {a : α} : ∃ A, Axioms.T A ∉ (@LogicEMB4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMB4.sound frame_1_3 (hcon #a))

end LogicEMB4

theorem LogicEMB_ssubset_LogicEMB4 : @LogicEMB ℕ ⊂ LogicEMB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMB.not_provable_axiomFour (a := (0 : ℕ))
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMC45_ssubset_LogicEMB4 : @LogicEMC45 ℕ ⊂ LogicEMB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomFour |
        exact Logic.axiomFive
  · obtain ⟨A, hA⟩ := LogicEMC45.not_provable_axiomB (a := (0 : ℕ))
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECB4_ssubset_LogicEMB4 : @LogicECB4 ℕ ⊂ LogicEMB4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomB
    · exact Logic.axiomFour
  · obtain ⟨A, B, hA⟩ := LogicECB4.not_provable_axiomM (a := (0 : ℕ)) (b := 1) (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
