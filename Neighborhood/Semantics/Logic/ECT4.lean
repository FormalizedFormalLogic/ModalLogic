module

public import Neighborhood.Semantics.Logic.ET4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame3_10520744

/-!
# The neighborhood logic `LogicECT4`

Soundness and consistency of `LogicECT4`, the classical modal logic axiomatised by the regularity
axiom `C`, the reflexivity axiom `T`, and the transitivity axiom `Four`, with respect to the
regular, reflexive, and transitive neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicECT4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsReflexive]
    [F.IsTransitive] :
    A ∈ LogicECT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicECT4.consistent : (@LogicECT4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicECT4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECT4 α)) :=
  MaximalConsistentSet.nonempty LogicECT4.consistent

theorem LogicET4_ssubset_LogicECT4 : @LogicET4 ℕ ⊂ LogicECT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicET4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_10520744.not_valid_axiomC (LogicET4.sound frame_3_10520744 hC)

end
