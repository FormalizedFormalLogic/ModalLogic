module

public import ModalLogicArchive.Modal.Kripke.Logic.KTB
public import ModalLogicArchive.Modal.Kripke.Logic.KD45
public import ModalLogicArchive.Modal.Kripke.Logic.KB4
public import ModalLogicArchive.Modal.Kripke.Logic.S4Point4
public import ModalLogicArchive.Vorspiel.Rel.Universal

@[expose] public section

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

variable {F : Frame}

class Frame.IsUniversal (F : Frame) extends _root_.IsUniversal F.Rel
@[simp] lemma universal [F.IsUniversal] : ∀ {x y : F.World}, x ≺ y := by apply IsUniversal.universal;

instance [F.IsUniversal] : F.IsEuclidean := by simp
instance [F.IsUniversal] : F.IsPreorder where

protected class Frame.IsS5 (F : Frame) extends F.IsReflexive, F.IsEuclidean
protected class Frame.IsFiniteS5 (F : Frame) extends F.IsFinite, F.IsS5

instance [F.IsS5] : F.IsKD45 where
instance [F.IsS5] : F.IsKB4 where
instance [F.IsS5] : F.IsKTB where
instance [F.IsS5] : F.IsS4Point4 where

protected abbrev FrameClass.S5 : FrameClass := { F | F.IsS5 }
protected abbrev FrameClass.finite_S5: FrameClass := { F | F.IsFiniteS5 }
protected abbrev FrameClass.universal : FrameClass := { F | F.IsUniversal }

instance Frame.pointGenerate.instIsUniversal {F : Frame} {r : F.World} [F.IsS5] : (F↾r).IsUniversal where
  universal := by
    rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩;
    . simp;
    . grind;
    . suffices x ≺ y by simpa;
      exact Std.Symm.symm _ _ hx;
    . suffices x ≺ y by simpa;
      apply F.eucl hx hy;

lemma iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass : FrameClass.universal ⊧ φ ↔ FrameClass.S5 ⊧ φ := by
  constructor;
  . rintro h F hF V r;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply Model.pointGenerate.modal_equivalent_at_root r |>.mp;
    apply h;
    simp only [Set.mem_setOf_eq];
    infer_instance;
  . rintro h F F_univ;
    apply h;
    simp_all;
    constructor;

end Kripke

instance : Sound Modal.S5 FrameClass.S5 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFive_of_euclidean;

instance : Sound Modal.S5 FrameClass.universal := ⟨by
  intro φ hF;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mpr;
  exact Sound.sound (𝓜 := FrameClass.S5) hF;
⟩

instance : Entailment.Consistent Modal.S5 := consistent_of_sound_frameclass FrameClass.S5 $ by
  use whitepoint;
  constructor;

instance : Canonical Modal.S5 FrameClass.S5 := ⟨by constructor⟩

instance : Complete Modal.S5 FrameClass.S5 := inferInstance

instance : Complete Modal.S5 FrameClass.universal := ⟨by
  intro φ hF;
  apply Complete.complete (𝓜 := FrameClass.S5);
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mp;
  exact hF;
⟩

instance : Modal.KTB ⪱ Modal.S5 := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass (FrameClass.KTB) (FrameClass.S5);
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Five (.atom 0);
    constructor;
    . exact axiomFive!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KTB)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0) ∨ (x = 1 ∧ y ≠ 2) ∨ (x = 2 ∧ y ≠ 1)⟩, λ _ x => x = 1⟩;
      use M, 0;
      constructor;
      . refine { refl := by omega, symm := by omega };
      . suffices (0 : M.World) ≺ 1 ∧ ∃ x : M.World, (0 : M.World) ≺ x ∧ ¬x ≺ 1 by
          simpa [M, Semantics.Models, Satisfies];
        constructor;
        . omega;
        . use 2;
          constructor <;> omega;

instance : Modal.KD45 ⪱ Modal.S5 := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass (FrameClass.KD45) (FrameClass.S5);
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KD45)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 1)⟩, λ _ x => x = 1⟩;
      use M, 0;
      constructor;
      . refine {
          serial := by intro x; use 1; omega;,
          trans := by omega,
          reucl := by simp [RightEuclidean]; omega
        }
      . simp [Semantics.Models, Satisfies, M];
        grind;

instance : Modal.KB4 ⪱ Modal.S5 := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass (FrameClass.KB4) (FrameClass.S5);
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KB4)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ _ x => False⟩, 0;
      constructor;
      . refine { symm := by tauto, trans := by tauto };
      . simp [Semantics.Models, Satisfies];

instance : Modal.S4Point4 ⪱ Modal.S5 := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass (FrameClass.S4Point4) (FrameClass.S5);
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Five (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.S4Point4)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ a w => w = 0⟩;
      use M, 0;
      constructor;
      . refine {
          sobocinski := by
            intro x y z _ _;
            match x, y with
            | 0, 0 => contradiction;
            | 0, 1 => omega;
            | 1, 0 => contradiction;
            | 1, 1 => contradiction;
        };
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x : M.World, (0 : M) ≺ x ∧ ¬x ≺ 0 by
          simp [M, Semantics.Models, Satisfies];
          grind;
        constructor;
        . omega;
        . use 1;
          constructor <;> omega;

instance : Modal.S4 ⪱ Modal.S5 := calc
  Modal.S4 ⪱ Modal.S4Point2 := by infer_instance
  _          ⪱ Modal.S4Point3 := by infer_instance
  _          ⪱ Modal.S4Point4 := by infer_instance
  _          ⪱ Modal.S5       := by infer_instance

instance : Entailment.S4 Modal.S5 where
  Four φ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Entailment.WeakerThan.pbl (𝓢 := Modal.S4);
    simp;

instance : Modal.KT ⪱ Modal.S5 := calc
  Modal.KT ⪱ Modal.S4 := by infer_instance
  _        ⪱ Modal.S5 := by infer_instance

end LO.Modal
end
