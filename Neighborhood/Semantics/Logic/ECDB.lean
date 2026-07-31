module

public import Neighborhood.Semantics.Logic.ECD
public import Neighborhood.Semantics.Logic.ECB
public import Neighborhood.Semantics.Logic.EDB

/-!
# The neighborhood logic `LogicECDB`

Soundness and consistency of `LogicECDB`, the classical modal logic axiomatised by the regularity
axiom `C`, the seriality axiom `D`, and the symmetry axiom `B`, with respect to the regular,
serial, and symmetric neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECDB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial]
    [F.IsSymmetric] :
    A ∈ LogicECDB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECDB.sound frame_1_2 hC⟩

end LogicECDB

theorem LogicECD_ssubset_LogicECDB : @LogicECD ℕ ⊂ LogicECDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECD.not_provable_axiomB (0 : ℕ)
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECB_ssubset_LogicECDB : @LogicECB ℕ ⊂ LogicECDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECB.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEDB_ssubset_LogicECDB : @LogicEDB ℕ ⊂ LogicECDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEDB.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
