module

public import Neighborhood.Semantics.Logic.EMT
public import Neighborhood.Semantics.Logic.ET4
public import Neighborhood.Semantics.Logic.EMD4

/-!
# The neighborhood logic `LogicEMT4`

Soundness, consistency and completeness of `LogicEMT4`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the reflexivity axiom `T` and the transitivity axiom `Four`, with
respect to the neighborhood frames that are monotonic, reflexive and transitive, together with its
finite frame property.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMT4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsReflexive] [F.IsTransitive] :
    A ∈ LogicEMT4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMT4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMT4.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsReflexive] →
      [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMT4 α :=
  (supplementedBasicCanonicalModel LogicEMT4).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMT4).toFrame
      (supplementedBasicCanonicalModel LogicEMT4).Val)

theorem finite_complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.IsMonotonic] → [F.IsReflexive] →
      [F.IsTransitive] → F ⊧ A) : A ∈ @LogicEMT4 α :=
  LogicEMT4.complete <| by
    intro κ _ F hMono hRefl hTrans V x
    let M : Model κ α := ⟨F, V⟩
    haveI : Finite (FilterEqvQuotient M A.subformulas) := FilterEqvQuotient.finite (by simp)
    apply (supplementedTransitiveFiltration M A.subformulas).filtration_satisfies _
      (by grind) |>.mp
    haveI : (supplementedTransitiveFiltration M A.subformulas).toModel.toFrame.IsFinite := ⟨‹_›⟩
    exact h (supplementedTransitiveFiltration M A.subformulas).toModel.toFrame
      (supplementedTransitiveFiltration M A.subformulas).toModel.Val ⟦x⟧

lemma not_provable_axiomC {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMT4 α) := by
  by_contra! hcon
  exact frame_3_10520744.not_valid_axiomC hab (LogicEMT4.sound frame_3_10520744 (hcon #a #b))

omit [DecidableEq α] in
lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMT4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMT4.sound frame_1_0 hcon)

end LogicEMT4

theorem LogicEMT_ssubset_LogicEMT4 : @LogicEMT ℕ ⊂ LogicEMT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEMT.not_provable_axiomFour (a := (0 : ℕ))
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicET4_ssubset_LogicEMT4 : @LogicET4 ℕ ⊂ LogicEMT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicET4.not_provable_axiomM (a := (0 : ℕ)) (b := 1) (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMD4_ssubset_LogicEMT4 : @LogicEMD4 ℕ ⊂ LogicEMT4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩)
    · exact ProvableHilbert.axm (by grind)
    · exact Logic.axiomD
    · exact ProvableHilbert.axm (by grind)
  · obtain ⟨A, hA⟩ := LogicEMD4.not_provable_axiomT (a := (0 : ℕ))
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end
