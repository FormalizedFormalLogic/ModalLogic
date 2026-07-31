module

public import Neighborhood.Semantics.Logic.E4
public import Neighborhood.Semantics.Logic.EM
public import Neighborhood.Semantics.Example.Frame2_206

/-!
# The neighborhood logic `LogicEM4`

Soundness, consistency and completeness of `LogicEM4`, the classical modal logic axiomatised by
the monotonicity axiom `M` and the transitivity axiom `Four`, with respect to the neighborhood
frames that are monotonic and transitive, together with its finite frame property.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEM4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsTransitive] :
    A ∈ LogicEM4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEM4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEM4.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsTransitive] → F ⊧ A) :
    A ∈ @LogicEM4 α :=
  (supplementedBasicCanonicalModel LogicEM4).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEM4).toFrame
      (supplementedBasicCanonicalModel LogicEM4).Val)

theorem finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.IsMonotonic] →
      [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEM4 α :=
  LogicEM4.complete <| by
    intro κ _ F hMono hTrans V x
    let M : Model κ α := ⟨F, V⟩
    haveI : Finite (FilterEqvQuotient M A.subformulas) := FilterEqvQuotient.finite (by simp)
    apply (supplementedTransitiveFiltration M A.subformulas).filtration_satisfies _
      (by grind) |>.mp
    haveI : (supplementedTransitiveFiltration M A.subformulas).toModel.toFrame.IsFinite := ⟨‹_›⟩
    exact h (supplementedTransitiveFiltration M A.subformulas).toModel.toFrame
      (supplementedTransitiveFiltration M A.subformulas).toModel.Val ⟦x⟧

lemma not_provable_axiomC {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEM4 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab
    (LogicEM4.sound frame_2_206 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomD {a : α} : ∃ A, Axioms.D A ∉ (@LogicEM4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEM4.sound frame_1_3 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEM4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEM4.sound frame_1_0 hcon)

end LogicEM4

theorem LogicE4_ssubset_LogicEM4 : @LogicE4 ℕ ⊂ LogicEM4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicE4.not_provable_axiomM (a := (0 : ℕ)) (b := 1) (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEM_ssubset_LogicEM4 : @LogicEM ℕ ⊂ LogicEM4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEM.not_provable_axiomFour (a := (0 : ℕ))
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

end
