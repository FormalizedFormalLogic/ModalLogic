module

public import ModalLogicArchive.Modal.Kripke.Filtration


@[expose] public section

namespace LO.Modal

open Kripke

namespace Kripke

namespace Frame

variable {F : Frame} {n : ℕ}

class IsWeakTransitive (F : Kripke.Frame) (n : ℕ) where
  weak_trans : ∀ ⦃x y : F⦄, x ≺^[n + 1] y → x ≺^[n] y

instance [F.IsPiecewiseStronglyConnected] : F.IsPiecewiseConnected := inferInstance

lemma weak_trans [F.IsWeakTransitive n] : ∀ {x y : F.World}, x ≺^[n + 1] y → x ≺^[n] y := by
  apply IsWeakTransitive.weak_trans

instance [F.IsGeachConvergent ⟨0, n + 1, n, 0⟩] : F.IsWeakTransitive n := ⟨by
  rintro x y ⟨u, Rxu, Ruy⟩;
  have : ∀ u, x ≺ u → u ≺^[n] y → x ≺^[n] y := by
    simpa using @IsGeachConvergent.gconv (g := ⟨0, n + 1, n, 0⟩) (F := F) _ x x y;
  apply this u Rxu Ruy;
⟩
instance [F.IsWeakTransitive n] : F.IsGeachConvergent ⟨0, n + 1, n, 0⟩ := ⟨by
  suffices ∀ ⦃x y z : F⦄, x = y → ∀ (x_1 : F), x ≺ x_1 → x_1 ≺^[n] z → y ≺^[n] z by simpa using this;
  rintro x _ y rfl u Rxw Rwz;
  apply IsWeakTransitive.weak_trans;
  use u;
⟩

end Frame


variable {F : Kripke.Frame} {n : ℕ}

lemma validate_AxiomFourN_of_weakTransitive [weakTrans : F.IsWeakTransitive n] : F ⊧ (Axioms.FourN n (.atom 0)) := validate_axiomGeach_of_isGeachConvergent (g := ⟨0, n + 1, n, 0⟩)

namespace Canonical

variable {S} [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

instance [Entailment.HasAxiomFourN n 𝓢] : (canonicalFrame 𝓢).IsWeakTransitive n := by infer_instance;

end Canonical

end Kripke

end LO.Modal
end
