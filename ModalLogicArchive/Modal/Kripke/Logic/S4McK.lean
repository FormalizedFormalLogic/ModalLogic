module

public import ModalLogicArchive.Modal.Kripke.Logic.S4
public import ModalLogicArchive.Modal.Kripke.Logic.K4McK

@[expose] public section

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

variable {F : Kripke.Frame}

class Frame.IsS4McK (F : Kripke.Frame) extends F.IsReflexive, F.IsTransitive, F.SatisfiesMcKinseyCondition where

abbrev FrameClass.S4McK : FrameClass := { F | F.IsS4McK }

end Kripke



namespace S4McK.Kripke

instance : Sound Modal.S4McK FrameClass.S4McK := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomMcK_of_satisfiesMcKinseyCondition;

instance : Entailment.Consistent Modal.S4McK := consistent_of_sound_frameclass FrameClass.S4McK $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  constructor

instance : Canonical Modal.S4McK FrameClass.S4McK := ⟨by constructor⟩

instance : Complete Modal.S4McK FrameClass.S4McK := inferInstance


instance : Modal.S4 ⪱ Modal.S4McK := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.McK (.atom 0));
    constructor;
    . exact axiomMcK!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.S4)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ _ w => w = 0⟩;
      use M, 0;
      constructor;
      . refine {
          refl := by tauto;
          trans := by tauto;
        }
      . suffices ∃ x, x ≠ (0 : M.World) by simp [M, Transitive, Reflexive, Semantics.Models, Satisfies];
        use 1;
        trivial;

instance : Modal.K4McK ⪱ Modal.S4McK := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_subset_axioms; intro φ; aesop;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K4McK)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => y = 1⟩, λ _ w => w = 1⟩;
      use M, 0;
      constructor;
      . exact {
          trans := by omega;
          mckinsey := by
            simp only [Fin.isValue, forall_eq, and_self, M];
            intro;
            use 1;
        }
      . simp [Semantics.Models, Satisfies, M];

end S4McK.Kripke

end LO.Modal
end
