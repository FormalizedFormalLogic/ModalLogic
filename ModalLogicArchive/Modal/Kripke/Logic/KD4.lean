module

public import ModalLogicArchive.Modal.Kripke.Logic.K4
public import ModalLogicArchive.Modal.Kripke.Logic.KD

@[expose] public section

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

protected class Frame.IsKD4 (F : Kripke.Frame) extends F.IsSerial, F.IsTransitive

protected abbrev FrameClass.KD4 : FrameClass := { F | F.IsKD4 }

end Kripke


namespace KD4

instance : Sound Modal.KD4 FrameClass.KD4 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomFour_of_transitive;

instance : Entailment.Consistent Modal.KD4 := consistent_of_sound_frameclass
  FrameClass.KD4 $ by
    use whitepoint;
    constructor

instance : Canonical Modal.KD4 FrameClass.KD4 := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor
⟩

instance : Complete Modal.KD4 FrameClass.KD4 := inferInstance

end KD4

instance : Modal.KD ⪱ Modal.KD4 := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KD)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Bool, λ x y => x != y⟩, λ _ w => w = true⟩, false;
      constructor;
      . exact { serial := by simp [Serial]; };
      . simp [Semantics.Models, Satisfies];
        tauto;

instance : Modal.K4 ⪱ Modal.KD4 := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K4)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ _ w => w = 0⟩, 0;
      constructor;
      . exact { trans := by simp; }
      . simp [Semantics.Models, Satisfies];

end LO.Modal
end
