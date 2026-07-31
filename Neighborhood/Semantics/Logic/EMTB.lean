module

public import Neighborhood.Semantics.Logic.EMDB
public import Neighborhood.Semantics.Logic.EMCNT
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_140

/-!
# The neighborhood logic `LogicEMTB`

Soundness and consistency of `LogicEMTB`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the reflexivity axiom `T` and the symmetry axiom `B`, with respect to the
neighborhood frames that are monotonic, reflexive and symmetric.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMTB.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsReflexive]
    [F.IsSymmetric] :
    A ∈ LogicEMTB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEMTB.consistent : (@LogicEMTB α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMTB.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMTB α)) :=
  MaximalConsistentSet.nonempty LogicEMTB.consistent

theorem LogicEMDB_ssubset_LogicEMTB : @LogicEMDB ℕ ⊂ LogicEMTB := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomD | exact Logic.axiomB
  · intro h
    have hT : Axioms.T #0 ∈ (@LogicEMDB ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomT (LogicEMDB.sound frame_2_140 hT)

theorem LogicEMCNT_ssubset_LogicEMTB : @LogicEMCNT ℕ ⊂ LogicEMTB := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT
  · intro h
    have hB : Axioms.B #0 ∈ (@LogicEMCNT ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomB (LogicEMCNT.sound frame_2_138 hB)

end
