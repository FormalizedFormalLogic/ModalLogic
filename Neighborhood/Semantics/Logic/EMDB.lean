module

public import Neighborhood.Semantics.Logic.EMCND
public import Neighborhood.Semantics.Logic.EMB

/-!
# The neighborhood logic `LogicEMDB`

Soundness and consistency of `LogicEMDB`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the seriality axiom `D`, and the symmetry axiom `B`, with respect to the
neighborhood frames that are monotonic, serial, and symmetric.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMDB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSerial]
    [F.IsSymmetric] :
    A ∈ LogicEMDB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMDB.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEMDB.sound frame_2_140 (hcon #a))

end LogicEMDB

theorem LogicEMCND_ssubset_LogicEMDB : @LogicEMCND ℕ ⊂ LogicEMDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD
  · obtain ⟨A, hA⟩ := LogicEMCND.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMB_ssubset_LogicEMDB : @LogicEMB ℕ ⊂ LogicEMDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMB.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
