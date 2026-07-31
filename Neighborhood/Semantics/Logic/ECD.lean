module

public import Neighborhood.Semantics.Logic.EC
public import Neighborhood.Semantics.Logic.ED

/-!
# The neighborhood logic `LogicECD`

Soundness and consistency of `LogicECD`, the classical modal logic axiomatised by both the
regularity axiom `C` and the seriality axiom `D`, with respect to the regular and serial
neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECD

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial] :
    A ∈ LogicECD → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECD α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECD.sound frame_1_2 hC⟩

lemma not_provable_axiomB {a : α} : ∃ A, Axioms.B A ∉ (@LogicECD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicECD.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFive {a : α} : ∃ A, Axioms.Five A ∉ (@LogicECD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicECD.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour {a : α} : ∃ A, Axioms.Four A ∉ (@LogicECD α) := by
  by_contra! hcon
  exact frame_1_1.not_valid_axiomFour (LogicECD.sound frame_1_1 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicECD α) := by
  intro hcon
  exact frame_1_1.not_valid_axiomP (LogicECD.sound frame_1_1 hcon)

end LogicECD

theorem LogicEC_ssubset_LogicECD : @LogicEC ℕ ⊂ LogicECD := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEC.not_provable_axiomD (a := (0 : ℕ))
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicED_ssubset_LogicECD : @LogicED ℕ ⊂ LogicECD := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · obtain ⟨A, B, hA⟩ := LogicED.not_provable_axiomC (a := (0 : ℕ)) (b := 1) (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

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
