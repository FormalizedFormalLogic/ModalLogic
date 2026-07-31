module

public import Neighborhood.Semantics.Logic.ECD
public import Neighborhood.Semantics.Logic.ECB
public import Neighborhood.Semantics.Logic.EDB
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_3346281

/-!
# The neighborhood logic `LogicECDB`

Soundness and consistency of `LogicECDB`, the classical modal logic axiomatised by the regularity
axiom `C`, the seriality axiom `D`, and the symmetry axiom `B`, with respect to the regular,
serial, and symmetric neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicECDB.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial]
    [F.IsSymmetric] :
    A ∈ LogicECDB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECDB.sound frame_1_2 hC⟩

theorem LogicECD_ssubset_LogicECDB : @LogicECD ℕ ⊂ LogicECDB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hB : Axioms.B #0 ∈ @LogicECD ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomB (LogicECD.sound frame_1_0 hB)

theorem LogicECB_ssubset_LogicECDB : @LogicECB ℕ ⊂ LogicECDB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ @LogicECB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicECB.sound frame_1_3 hD)

theorem LogicEDB_ssubset_LogicECDB : @LogicEDB ℕ ⊂ LogicECDB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicEDB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_3346281.not_valid_axiomC (LogicEDB.sound frame_3_3346281 hC)

end
