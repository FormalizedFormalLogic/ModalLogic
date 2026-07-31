module

public import Neighborhood.Semantics.Logic.ET4
public import Neighborhood.Semantics.Logic.ECT
public import Neighborhood.Semantics.Logic.ECD4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_8
public import Neighborhood.Semantics.Example.Frame2_170
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

instance : (@LogicECT4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECT4.sound frame_1_2 hC⟩

theorem LogicET4_ssubset_LogicECT4 : @LogicET4 ℕ ⊂ LogicECT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicET4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_10520744.not_valid_axiomC (LogicET4.sound frame_3_10520744 hC)

theorem LogicECT_ssubset_LogicECT4 : @LogicECT ℕ ⊂ LogicECT4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFour : Axioms.Four #0 ∈ @LogicECT ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_8.not_valid_axiomFour (LogicECT.sound frame_2_8 hFour)

theorem LogicECD4_ssubset_LogicECT4 : @LogicECD4 ℕ ⊂ LogicECT4 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩)
    · exact ProvableHilbert.axm (by grind)
    · exact Logic.axiomD
    · exact ProvableHilbert.axm (by grind)
  · intro h
    have hT : Axioms.T #0 ∈ @LogicECD4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_170.not_valid_axiomT (LogicECD4.sound frame_2_170 hT)

end
