module

public import Neighborhood.Semantics.Logic.E
public import Neighborhood.Semantics.Filtration
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_10520744


@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicE4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsTransitive] : A ∈ LogicE4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ⟨_, rfl⟩; simp)

instance : (@LogicE4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicE4.sound frame_1_2 hC⟩

theorem complete [DecidableEq α]
  (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsTransitive] → F ⊧ A) :
  A ∈ @LogicE4 α :=
  (basicCanonicalModel LogicE4).mem_of_valid
    (h (basicCanonicalModel LogicE4).toFrame
      (basicCanonicalModel LogicE4).Val)

theorem finite_complete [DecidableEq α]
  (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsFinite] → [F.IsTransitive] → F ⊧ A) :
  A ∈ @LogicE4 α := LogicE4.complete <| by
    intro κ _ F hF V x;
    let M : Model κ α := ⟨F, V⟩
    haveI : Finite (FilterEqvQuotient M A.subformulas) := FilterEqvQuotient.finite (by simp)
    apply (transitiveFiltration M A.subformulas).filtration_satisfies _ (by grind) |>.mp
    haveI : (transitiveFiltration M A.subformulas).toModel.toFrame.IsFinite := ⟨‹_›⟩
    exact h (transitiveFiltration M A.subformulas).toModel.toFrame
      (transitiveFiltration M A.subformulas).toModel.Val ⟦x⟧

lemma not_provable_axiomC [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicE4 α) := by
  by_contra! hcon
  exact frame_3_10520744.not_valid_axiomC hab (LogicE4.sound frame_3_10520744 (hcon #a #b))

lemma not_provable_axiomD {a : α} : ∃ A, Axioms.D A ∉ (@LogicE4 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD
    (LogicE4.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFive {a : α} : ∃ A, Axioms.Five A ∉ (@LogicE4 α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive
    (LogicE4.sound frame_1_0 (hcon #a))

lemma not_provable_axiomM [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ∃ A B, Axioms.M A B ∉ (@LogicE4 α) := by
  by_contra! hcon
  exact frame_3_9471106.not_valid_axiomM hab (LogicE4.sound frame_3_9471106 (hcon #a #b))

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicE4 α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicE4.sound frame_1_0 hcon)

end LogicE4


theorem LogicE_ssubset_LogicE4 : @LogicE ℕ ⊂ LogicE4 := by
  apply Set.ssubset_iff_exists.mpr;
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.empty_subset _)
  · obtain ⟨A, hA⟩ := LogicE.not_provable_axiomFour (a := 0);
    use Axioms.Four A;
    constructor;
    . grind;
    . assumption;


end
