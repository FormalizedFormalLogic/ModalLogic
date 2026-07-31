module

public import Neighborhood.Semantics.Logic.ETB
public import Neighborhood.Semantics.Logic.ECNDB
public import Neighborhood.Semantics.Logic.ECNT
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame3_9488552
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame2_138

/-!
# The neighborhood logic `LogicECTB`

Soundness and consistency of `LogicECTB`, the classical modal logic axiomatised by the
regularity axiom `C`, the reflexivity axiom `T`, and the symmetry axiom `B`, with respect to the
neighborhood frames that are regular, reflexive, and symmetric.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicECTB.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsReflexive]
    [F.IsSymmetric] :
    A ∈ LogicECTB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicECTB.consistent : (@LogicECTB α).IsConsistent := by
  by_contra! hC
  simpa using LogicECTB.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECTB α)) :=
  MaximalConsistentSet.nonempty LogicECTB.consistent

theorem LogicETB_ssubset_LogicECTB : @LogicETB ℕ ⊂ LogicECTB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicETB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_9488552.not_valid_axiomC (LogicETB.sound frame_3_9488552 hC)

theorem LogicECNDB_ssubset_LogicECTB : @LogicECNDB ℕ ⊂ LogicECTB := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomB
  · intro h
    have hT : Axioms.T #0 ∈ @LogicECNDB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomT (LogicECNDB.sound frame_2_140 hT)

theorem LogicECNT_ssubset_LogicECTB : @LogicECNT ℕ ⊂ LogicECTB := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomT
  · intro h
    have hB : Axioms.B #0 ∈ @LogicECNT ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomB (LogicECNT.sound frame_2_138 hB)

end
