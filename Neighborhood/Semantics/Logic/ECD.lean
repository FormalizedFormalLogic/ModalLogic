module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_10528928

/-!
# The neighborhood logic `LogicECD`

Soundness and consistency of `LogicECD`, the classical modal logic axiomatised by both the
regularity axiom `C` and the seriality axiom `D`, with respect to the regular and serial
neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicECD.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial] :
    A ∈ LogicECD → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECD α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECD.sound frame_1_2 hC⟩

theorem LogicEC_ssubset_LogicECD : @LogicEC ℕ ⊂ LogicECD := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEC ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEC.sound frame_1_3 hD)

theorem LogicED_ssubset_LogicECD : @LogicED ℕ ⊂ LogicECD := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicED ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_10528928.not_valid_axiomC (LogicED.sound frame_3_10528928 hC)

section

variable [DecidableEq α]

theorem LogicECD.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsRegular] → [F.IsSerial] → F ⊧ A) :
    A ∈ @LogicECD α :=
  (basicCanonicalModel LogicECD).mem_of_valid
    (h (basicCanonicalModel LogicECD).toFrame
      (basicCanonicalModel LogicECD).Val)

end

end
