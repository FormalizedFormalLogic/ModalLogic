module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Logic.EP
public import Neighborhood.Semantics.Logic.ECD
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame2_78

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicECP.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.NotContainsEmpty] :
    A ∈ LogicECP → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

instance : (@LogicECP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECP.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem LogicECP.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsRegular] → [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicECP α :=
  (basicCanonicalModel LogicECP).mem_of_valid
    (h (basicCanonicalModel LogicECP).toFrame
      (basicCanonicalModel LogicECP).Val)

theorem LogicECD_ssubset_LogicECP : @LogicECD ℕ ⊂ LogicECP := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, C, rfl⟩ | ⟨B, rfl⟩) <;> first | exact Logic.axiomC | exact Logic.axiomD
  · intro h
    have hP : (Axioms.P : Formula ℕ) ∈ @LogicECD ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_1.not_valid_axiomP (LogicECD.sound frame_1_1 hP)

theorem LogicEP_ssubset_LogicECP : @LogicEP ℕ ⊂ LogicECP := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hC : (Axioms.C #0 #1 : Formula ℕ) ∈ @LogicEP ℕ := h (Logic.HasAxiomC.C _ _)
    exact frame_2_78.not_valid_axiomC (LogicEP.sound frame_2_78 hC)

end
