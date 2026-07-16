module

public import ModalLogicArchive.Modal.Kripke.Logic.K5
public import ModalLogicArchive.Modal.Kripke.Logic.KD

@[expose] public section

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

protected class Frame.IsKD5 (F : Kripke.Frame) extends F.IsSerial, F.IsEuclidean
protected abbrev FrameClass.KD5 : FrameClass := { F | F.IsKD5 }

end Kripke

instance : Sound (Modal.KD5) Kripke.FrameClass.KD5 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomFive_of_euclidean;

instance : Entailment.Consistent (Modal.KD5) := consistent_of_sound_frameclass Kripke.FrameClass.KD5 $ by
  use whitepoint;
  constructor;

instance : Canonical (Modal.KD5) Kripke.FrameClass.KD5 := ⟨by constructor⟩

instance : Complete (Modal.KD5) Kripke.FrameClass.KD5 := inferInstance

instance : Modal.KD ⪱ Modal.KD5 := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Five (.atom 0));
    constructor;
    . exact axiomFive!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KD)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ _ w => w = 0⟩;
      use M, 0;
      constructor;
      . tauto;
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simp [M, Semantics.Models, Satisfies];
          grind;
        constructor;
        . tauto;
        . use 1;
          constructor <;> tauto;

instance : Modal.K5 ⪱ Modal.KD5 := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K5)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ _ w => w = 0⟩, 0;
      constructor;
      . refine { reucl := by simp [RightEuclidean]; };
      . simp [Semantics.Models, Satisfies];

end LO.Modal
end
