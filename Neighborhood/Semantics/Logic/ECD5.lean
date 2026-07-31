module

public import Neighborhood.Semantics.Logic.ECD
public import Neighborhood.Semantics.Logic.EC5
public import Neighborhood.Semantics.Logic.ED5
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_10528928

/-!
# The neighborhood logic `LogicECD5`

Soundness and consistency of `LogicECD5`, the classical modal logic axiomatised by the regularity
axiom `C`, the seriality axiom `D`, and the euclideanity axiom `5`, with respect to the regular,
serial, and euclidean neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicECD5.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial]
    [F.IsEuclidean] :
    A ∈ LogicECD5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECD5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECD5.sound frame_1_2 hC⟩

theorem LogicECD_ssubset_LogicECD5 : @LogicECD ℕ ⊂ LogicECD5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFive : Axioms.Five #0 ∈ @LogicECD ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomFive (LogicECD.sound frame_1_0 hFive)

theorem LogicEC5_ssubset_LogicECD5 : @LogicEC5 ℕ ⊂ LogicECD5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEC5 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEC5.sound frame_1_3 hD)

theorem LogicED5_ssubset_LogicECD5 : @LogicED5 ℕ ⊂ LogicECD5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicED5 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_10528928.not_valid_axiomC (LogicED5.sound frame_3_10528928 hC)

end
