module

public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Logic.EP

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.NotContainsEmpty] :
    A ∈ LogicEMP → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

instance : (@LogicEMP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMP.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicEMP α :=
  (supplementedBasicCanonicalModel LogicEMP).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMP).toFrame
      (supplementedBasicCanonicalModel LogicEMP).Val)

omit [DecidableEq α] in
lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMP α) := by
  by_contra! hcon
  exact frame_2_238.not_valid_axiomD (LogicEMP.sound frame_2_238 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMP α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMP.sound frame_1_0 hcon)

end LogicEMP

theorem LogicEM_ssubset_LogicEMP : @LogicEM ℕ ⊂ LogicEMP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · exact ⟨Axioms.P, (ProvableHilbert.axm (by grind)), LogicEM.not_provable_axiomP⟩

theorem LogicEP_ssubset_LogicEMP : @LogicEP ℕ ⊂ LogicEMP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicEP.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (Logic.HasAxiomM.M _ _), hA⟩

end
