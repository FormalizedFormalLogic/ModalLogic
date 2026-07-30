module

public import ModalNeighborhood.Semantics.Logic.E4
public import ModalNeighborhood.Semantics.Logic.ET

@[expose] public section

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsET4 (F : Frame) extends F.IsReflexive, F.IsTransitive
protected class Frame.IsFiniteET4 (F : Frame) extends F.IsET4, F.IsFinite

protected abbrev FrameClass.ET4 : FrameClass := { F | F.IsET4 }
protected abbrev FrameClass.finite_ET4 : FrameClass := { F | F.IsFiniteET4 }

end Neighborhood



namespace ET4

instance Neighborhood.sound : Sound Modal.ET4 FrameClass.ET4 := instSound_of_validates_axioms $ by
  constructor;
  rintro φ (rfl | rfl) F ⟨_, _⟩;
  . apply valid_axiomFour_of_isTransitive;
  . apply valid_axiomT_of_isReflexive;

instance consistent : Entailment.Consistent Modal.ET4 := consistent_of_sound_frameclass FrameClass.ET4 $ by
  use Frame.simple_blackhole;
  constructor;

instance Neighborhood.complete : Complete Modal.ET4 FrameClass.ET4 := (basicCanonicity _).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

-- Awaiting the port of `ModalNeighborhood.Semantics.Filtration`, on which the filtration construction depends.
/-
/-- FFP of `Modal.ET4` -/
instance Neighborhood.finite_complete : Complete Modal.ET4 FrameClass.finite_ET4 := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.ET4);
  intro F F_trans V x;
  replace F_trans := Set.mem_setOf_eq.mp F_trans;

  let M : Model := ⟨F, V⟩;
  apply transitiveFiltration M φ.subformulas |>.filtration_satisfies _ (by grind) |>.mp;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  exact {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    trans := by apply transitiveFiltration.isTransitive.trans;
    refl := by apply transitiveFiltration.isReflexive.refl;
  };
⟩
-/

end ET4

instance : Modal.E4 ⪱ Modal.ET4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E4);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 1, λ _ => Set.univ⟩;
      constructor;
      . tauto;
      . apply not_imp_not.mpr isReflexive_of_valid_axiomT;
        by_contra! hC;
        simpa [Frame.box] using @hC.refl ∅;

instance : Modal.ET ⪱ Modal.ET4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.ET);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, λ x => match x with | 0 => {Set.univ} | 1 => {{1}}⟩;
      constructor;
      . constructor;
        intro X x;
        match x with
        | 0 => rintro rfl; simp;
        | 1 => rintro rfl; simp;
      . by_contra! hC;
        have : ∀ (x : Fin 2), Set.univ ∈ match x with | 0 => ({Set.univ} : Set (Set (Fin 2))) | 1 => ({{1}} : Set (Set (Fin 2))) := by
          simpa [Frame.box, Set.eq_univ_iff_forall] using (Set.subset_def.mp $ isTransitive_of_valid_axiomFour hC |>.trans Set.univ) 0;
        replace : Set.univ = ({1} : Set (Fin 2)) := this 1;
        tauto_set;

end LO.Modal
end
