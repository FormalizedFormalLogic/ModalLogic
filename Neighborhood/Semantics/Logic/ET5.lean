module

public import Neighborhood.Semantics.Logic.END4
public import Neighborhood.Semantics.Logic.ENT4
public import Neighborhood.Semantics.Logic.E5

@[expose] public section

@[simp]
lemma Set.ne_univ_empty [Nonempty α] : Set.univ (α := α) ≠ ∅ := by simp only [ne_eq,
  univ_eq_empty_iff, not_isEmpty_of_nonempty, not_false_eq_true];

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsET5 (F : Frame) extends F.IsReflexive, F.IsEuclidean
protected abbrev FrameClass.ET5 : FrameClass := { F | F.IsET5 }

variable {F : Frame}

instance : Frame.simple_blackhole.IsET5 where
  eucl := by
    intro X x hx;
    simp_all [Frame.simple_blackhole, Frame.box];

section

variable [Entailment S (Formula ℕ)] {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.ET5 𝓢]

instance : (basicCanonicity 𝓢).toModel.IsEuclidean := by
  apply Canonicity.isEuclidean';
  intro X X_np A;
  suffices X ∉ (basicCanonicity 𝓢).𝒩 A → {w | X ∉ (basicCanonicity 𝓢).𝒩 w} ∈ (basicCanonicity 𝓢).𝒩 A by
    contrapose!;
    intro h1 h2;
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at h1 h2;
    exact h2 (this h1);
  intro h;
  have : {B | X ∉ (basicCanonicity 𝓢).𝒩 B} = proofset 𝓢 ⊤ := by
    suffices ∀ B, X ∉ (basicCanonicity 𝓢).𝒩 B by simpa [Set.eq_univ_iff_forall];
    rintro _ ⟨φ, _, hφ₂⟩;
    apply X_np φ;
    apply hφ₂;
  exact this ▸ (basicCanonicity 𝓢 |>.def_𝒩 A ⊤ |>.mp $ MaximalConsistentSet.mem_of_prove (by simp));

instance : (basicCanonicity 𝓢).toModel.IsET5 where

end

@[simp]
lemma counterframe_2_3_5.not_valid_axiomT : ¬counterframe_2_3_5 ⊧ Axioms.T (Formula.atom a) := by
  apply not_imp_not.mpr isReflexive_of_valid_axiomT;
  by_contra! hC;
  have := hC.refl {0};
  have := @this 1;
  grind;

instance : counterframe_axiomFive.IsENT4 where
  contains_unit := by simp [Frame.box];
  refl := by rintro X x (rfl | rfl | rfl) <;> tauto_set;
  trans := by rintro X x (rfl | rfl) <;> . dsimp [Frame.box]; grind;

end Neighborhood

namespace ET5

instance Neighborhood.sound : Sound Modal.ET5 FrameClass.ET5 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F (rfl | rfl) <;> simp;

instance consistent : Entailment.Consistent Modal.ET5 := consistent_of_sound_frameclass FrameClass.ET5 $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

instance Neighborhood.complete : Complete Modal.ET5 FrameClass.ET5 := (basicCanonicity Modal.ET5).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ET5

instance : Modal.ENT4 ⪱ Modal.ET5 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_provable_axioms;
    rintro φ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Five (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.ENT4);
      apply not_validOnFrameClass_of_exists_frame;
      use counterframe_axiomFive;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        infer_instance
      . simp;

instance : Modal.E5 ⪱ Modal.ET5 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E5);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, λ _ => Set.univ⟩;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        constructor;
        . intro X x hx;
          simp_all [Frame.box, Frame.dia];
      . apply not_imp_not.mpr isReflexive_of_valid_axiomT;
        by_contra! hC;
        have := hC.refl {1};
        have := @this 0;
        grind;

end LO.Modal
end
