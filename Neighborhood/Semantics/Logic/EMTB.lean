module

public import Neighborhood.Semantics.Logic.EMDB
public import Neighborhood.Semantics.Logic.EMCNT
public import Neighborhood.Semantics.Logic.ECTB
public import Neighborhood.Logic.Equiv.EMTB_EMCNTB

/-!
# The neighborhood logic `LogicEMTB`

Soundness and consistency of `LogicEMTB`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the reflexivity axiom `T` and the symmetry axiom `B`, with respect to the
neighborhood frames that are monotonic, reflexive and symmetric.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMTB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsReflexive]
    [F.IsSymmetric] :
    A ∈ LogicEMTB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMTB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMTB.sound frame_1_2 hC⟩

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMTB α) := by
  by_contra! hcon
  exact frame_3_8437920.not_valid_axiomFive (LogicEMTB.sound frame_3_8437920 (hcon #a))

end LogicEMTB

theorem LogicEMDB_ssubset_LogicEMTB : @LogicEMDB ℕ ⊂ LogicEMTB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomD | exact Logic.axiomB
  · obtain ⟨A, hA⟩ := LogicEMDB.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMCNT_ssubset_LogicEMTB : @LogicEMCNT ℕ ⊂ LogicEMTB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT
  · obtain ⟨A, hA⟩ := LogicEMCNT.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECTB_ssubset_LogicEMTB : @LogicECTB ℕ ⊂ LogicEMTB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · rw [LogicEMTB_eq_LogicEMCTB]
    exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicECTB.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
