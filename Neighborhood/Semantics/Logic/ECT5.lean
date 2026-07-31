module

public import Neighborhood.Semantics.Logic.ECTB
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame3_8437920

/-!
# The neighborhood logic `LogicECT5`

Soundness and consistency of `LogicECT5`, the classical modal logic axiomatised by the
regularity axiom `C`, the reflexivity axiom `T`, and the euclideanness axiom `Five`, with respect
to the neighborhood frames that are regular, reflexive, and euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicECT5.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsReflexive]
    [F.IsEuclidean] :
    A ∈ LogicECT5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicECT5.consistent : (@LogicECT5 α).IsConsistent := by
  by_contra! hC
  simpa using LogicECT5.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECT5 α)) :=
  MaximalConsistentSet.nonempty LogicECT5.consistent

theorem LogicECTB_ssubset_LogicECT5 : @LogicECTB ℕ ⊂ LogicECT5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomC | exact Logic.axiomT | exact Logic.axiomB
  · intro h
    have hFive : Axioms.Five #0 ∈ @LogicECTB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_8437920.not_valid_axiomFive (LogicECTB.sound frame_3_8437920 hFive)

end
