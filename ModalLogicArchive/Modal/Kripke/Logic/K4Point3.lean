module

public import ModalLogicArchive.Modal.Kripke.Logic.K4

@[expose] public section

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

protected class Frame.IsK4Point3 (F : Kripke.Frame) extends F.IsTransitive, F.IsPiecewiseConnected

abbrev FrameClass.K4Point3 : FrameClass := { F | F.IsK4Point3 }

end Kripke

instance : Sound Modal.K4Point3 FrameClass.K4Point3 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_WeakPoint3_of_weakConnected;

instance : Entailment.Consistent Modal.K4Point3 :=
  consistent_of_sound_frameclass FrameClass.K4Point3 $ by
    use whitepoint;
    constructor;

instance : Canonical Modal.K4Point3 FrameClass.K4Point3 :=  ⟨by constructor⟩

instance : Complete Modal.K4Point3 FrameClass.K4Point3 := inferInstance


instance : Modal.K4 ⪱ Modal.K4Point3 := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.WeakPoint3 (.atom 0) (.atom 1));
    constructor;
    . exact axiomWeakPoint3!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K4)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 3, λ x y => x = 0 ∧ y ≠ 0⟩,
        λ a w => if a = 0 then w = 1 else w = 2
      ⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        exact { trans := by omega }
      . suffices
          ∃ x : M.World, (0 : M.World) ≺ x ∧ x = 1 ∧ (∀ y, x ≺ y → y = 1) ∧ ¬x = 2 ∧
          ∃ x : M.World, (0 : M.World) ≺ x ∧ x = 2 ∧ (∀ z : M.World, x ≺ z → z = 2) ∧ x ≠ 1
          by simpa [M, Semantics.Models, Satisfies];
        refine ⟨1, ?_, rfl, ?_, ?_, 2, ?_, rfl, ?_, ?_⟩;
        . trivial;
        . omega;
        . trivial;
        . omega;
        . trivial;
        . trivial;

end LO.Modal
end
