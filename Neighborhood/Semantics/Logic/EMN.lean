module

public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Example.Frame2_140

/-!
# The neighborhood logic `LogicEMN`

Soundness, consistency and completeness of `LogicEMN`, the classical modal logic axiomatised by
the monotonicity axiom `M` together with `N := □⊤`, with respect to the monotonic frames
containing their unit.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMN

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.ContainsUnit] :
    A ∈ LogicEMN → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | rfl) <;> simp)

instance : (@LogicEMN α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMN.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] → F ⊧ A) :
    A ∈ @LogicEMN α :=
  (supplementedBasicCanonicalModel LogicEMN).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMN).toFrame
      (supplementedBasicCanonicalModel LogicEMN).Val)

lemma not_provable_axiomC (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMN α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab
    (LogicEMN.sound frame_2_206 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMN α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEMN.sound frame_2_140 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMN α) := by
  by_contra! hcon
  exact frame_2_172.not_valid_axiomFour (LogicEMN.sound frame_2_172 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMN α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMN.sound frame_1_3 hcon)

end LogicEMN

theorem LogicEM_ssubset_LogicEMN : @LogicEM ℕ ⊂ LogicEMN := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEM.not_provable_axiomN⟩

theorem LogicEN_ssubset_LogicEMN : @LogicEN ℕ ⊂ LogicEMN := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicEN.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
