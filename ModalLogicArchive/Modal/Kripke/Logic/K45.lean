module

public import ModalLogicArchive.Modal.Kripke.Logic.K4Point3
public import ModalLogicArchive.Modal.Kripke.Logic.K5

@[expose] public section

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

protected class Frame.IsK45 (F : Kripke.Frame) extends F.IsTransitive, F.IsEuclidean

protected abbrev FrameClass.K45 : FrameClass := { F | F.IsK45 }

instance {F : Kripke.Frame} [F.IsK45] : F.IsK4Point3 where

end Kripke


instance : Sound Modal.K45 FrameClass.K45 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomFive_of_euclidean;

instance : Entailment.Consistent Modal.K45 := consistent_of_sound_frameclass FrameClass.K45 $ by
  use whitepoint;
  constructor;

instance : Canonical Modal.K45 FrameClass.K45 := ⟨by constructor⟩

instance : Complete Modal.K45 FrameClass.K45 := inferInstance

instance : Modal.K5 ⪱ Modal.K45 := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms $ by rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K5);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0 ∧ y = 1) ∨ (x ≠ 0 ∧ y ≠ 0)⟩, λ _ w => w = 1⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        exact { reucl := by simp [RightEuclidean]; omega }
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ z, x ≺ z ∧ ¬z = 1 by
          simpa [M, Semantics.Models, Satisfies];
        constructor;
        . intro y; tauto;
        . exact ⟨1, by omega, 2, by omega, by trivial⟩;

instance : Modal.K4Point3 ⪱ Modal.K45 := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass FrameClass.K4Point3 FrameClass.K45;
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Five (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K4Point3);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 3, λ x y => x < y⟩,
        λ a w => w = 2
      ⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        refine {
          trans := by omega,
          p_connected := by simp [PiecewiseConnected, M]; omega;
        };
      . suffices (0 : M.World) ≺ 2 ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 2 by
          simpa [M, Semantics.Models, Satisfies];
        constructor;
        . omega;
        . use 2;
          omega;

end LO.Modal
end
