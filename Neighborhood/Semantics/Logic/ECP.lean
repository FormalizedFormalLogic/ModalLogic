module

public import Neighborhood.Semantics.Logic.EP
public import Neighborhood.Semantics.Logic.ECD
public import Neighborhood.Semantics.Example.Frame2_34

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.NotContainsEmpty] :
    A ∈ LogicECP → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

instance : (@LogicECP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECP.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsRegular] → [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicECP α :=
  (basicCanonicalModel LogicECP).mem_of_valid
    (h (basicCanonicalModel LogicECP).toFrame
      (basicCanonicalModel LogicECP).Val)

lemma not_provable_axiomM (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicECP α) := by
  by_contra! hcon
  exact frame_2_34.not_valid_axiomM hab (LogicECP.sound frame_2_34 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicECP α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicECP.sound frame_1_0 hcon)

end LogicECP

theorem LogicECD_ssubset_LogicECP : @LogicECD ℕ ⊂ LogicECP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, C, rfl⟩ | ⟨B, rfl⟩) <;> first | exact Logic.axiomC | exact Logic.axiomD
  · exact ⟨Axioms.P, (ProvableHilbert.axm (by grind)), LogicECD.not_provable_axiomP⟩

theorem LogicEP_ssubset_LogicECP : @LogicEP ℕ ⊂ LogicECP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicEP.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (Logic.HasAxiomC.C _ _), hA⟩

end
