module

public import Fin74.Logic.Shift
public import Fin74.Kripke.Chain

@[expose]
public section

namespace Fin74

variable {κ : Type*} {M : Model κ ℕ} {x y : M.World} {m : ℕ}

open Model.World

/-- `K1` climbs one level, by projection from the unfolding of `B (m+2)`: no hypotheses are
needed. -/
lemma forces_K1_succ : x ⊩ K1 (m + 1) := by grind [K1];

/-- The repair of the flawed auxiliary result (2) of [Fin74]: the paper's argument for `K2`
one level up is unsound in general (see the falsifying model recorded alongside this plan),
but it follows from the witness's `∼◇(A m)` obtained in the chain step instead. -/
lemma forces_K2_succ_of_not_dia_A (hA : x ⊩ ∼◇(A m)) : x ⊩ K2 (m + 1) := by
  rw [K2, forces_box];
  intro y Rxy hy;
  rw [C_add_two] at hy;
  simp only [forces_and] at hy;
  rw [forces_and];
  refine ⟨hy.1.1, ?_⟩;
  rw [forces_neg];
  intro hcon;
  have hAy : y ⊩ A m := by
    rw [A];
    simp only [forces_and];
    exact ⟨⟨hcon, hy.1.1⟩, hy.2⟩;
  exact hA ⟨y, Rxy, hAy⟩;

/-- `K3` climbs one level, from `K1` at the current level and transitivity. -/
lemma forces_K3_succ_of_K1 (h1 : x ⊩ K1 m) (Rxy : x ≺ y) : y ⊩ K3 (m + 1) := by
  grind [K1, K3];

/-- `K4` climbs one level, from `K2` at the current level and transitivity. -/
lemma forces_K4_succ_of_K2 (h2 : x ⊩ K2 m) (Rxy : x ≺ y) : y ⊩ K4 (m + 1) := by
  grind [K2, K4];

/-- The whole `K`-block climbs one level along a chain step, given the successor's
`∼◇(A m)`. -/
lemma forces_K_succ (hK : x ⊩ K m) (Rxy : x ≺ y) (hA : y ⊩ ∼◇(A m)) : y ⊩ K (m + 1) := by
  grind [K, forces_K1_succ, forces_K2_succ_of_not_dia_A, forces_K3_succ_of_K1, forces_K4_succ_of_K2];

/-- `D` persists to any successor that still forces `p₀ ⋎ p₁` (its two boxed conjuncts
persist along any accessible world). -/
lemma forces_D_of_rel (hD : x ⊩ D) (Rxy : x ≺ y) (hp : y ⊩ p0 ⋎ p1) : y ⊩ D := by
  grind [D];

/-- Auxiliary result (3) of [Fin74], repaired: if `M` strongly verifies `G` and `x` forces
`E⟦σ_m⟧`, then some strict successor of `x` forces `E⟦σ_{m+1}⟧`. -/
lemma chain_step (hG : M.StronglyVerifies G) (hx : x ⊩ E⟦shift m⟧) :
  ∃ y : M.World, x ≺ y ∧ ¬(y ≺ x) ∧ y ⊩ E⟦shift (m + 1)⟧ := by
  have hxF : x ⊩ F⟦shift m⟧ := hG (shift m) x hx;
  obtain ⟨y, Rxy, hy01, hyA, hyA'⟩ := forces_F_subst_shift.mp hxF;
  obtain ⟨hD, hAm, hK⟩ := forces_E_subst_shift.mp hx;
  have hstrict : ¬(y ≺ x) := by
    intro hyx;
    exact hyA (forces_dia_of_rel hAm hyx);
  refine ⟨y, Rxy, hstrict, forces_E_subst_shift.mpr ?_⟩;
  and_intros;
  · exact forces_D_of_rel hD Rxy hy01;
  · exact hyA';
  · exact forces_K_succ hK Rxy hyA;

/-- The valuation `ψ` of [Fin74]: `s` holds exactly at chain points of index `3i`, `t`
exactly at those of index `3i+1`. Only the atoms `s` (`#6`) and `t` (`#7`) matter; all other
atoms are false. -/
def psiVal {F : Frame κ} (u : ℕ → F.World) : F.World → ℕ → Prop
| v, 6 => ∃ i, v = u (3 * i)
| v, 7 => ∃ i, v = u (3 * i + 1)
| _, _ => False

variable {F : Frame κ} {u : ℕ → F.World}

/-- `s` holds exactly at chain points of index a multiple of `3`, on the ψ-model over an
injective chain `u`. -/
lemma forces_s_iff (hinj : Function.Injective u) (n : ℕ) : u n ⊩[⟨F, (psiVal u)⟩] s ↔ ∃ i, n = 3 * i := by
  constructor;
  · rintro ⟨i, hi⟩; exact ⟨i, hinj hi⟩;
  · rintro ⟨i, rfl⟩; use i;

/-- `t` holds exactly at chain points of index `1` more than a multiple of `3`, on the
ψ-model over an injective chain `u`. -/
lemma forces_t_iff (hinj : Function.Injective u) (n : ℕ) : u n ⊩[⟨F, (psiVal u)⟩] t ↔ ∃ i, n = 3 * i + 1 := by
  constructor;
  · rintro ⟨i, hi⟩; exact ⟨i, hinj hi⟩;
  · rintro ⟨i, rfl⟩; use i;

/-- On the ψ-model over any injective ascending chain along `F`, `∼H` is forced at the
chain's origin. Injectivity is essential: it lets the three phases `s`, `¬s ∧ t`, `¬s ∧ ¬t`
be told apart along the chain by their index mod 3. -/
lemma psi_forces_neg_H (hR : ∀ m, (u m) ≺ (u (m + 1))) (hinj : Function.Injective u) : u 0 ⊩[⟨F, (psiVal u)⟩] ∼H := by
  unfold H;
  rw [forces_neg, not_forces_neg, forces_and];
  and_intros;
  · exact (forces_s_iff hinj 0).mpr ⟨0, rfl⟩;
  · rw [forces_box];
    intro y hy hys;
    obtain ⟨i, rfl⟩ := hys;
    use u (3 * i + 1);
    constructor;
    . grind
    . simp only [forces_and];
      and_intros;
      · apply forces_s_iff hinj _ |>.not.mpr;
        grind;
      · exact (forces_t_iff hinj (3 * i + 1)).mpr ⟨i, rfl⟩;
      · use u (3 * i + 2);
        constructor;
        . grind;
        . simp only [forces_and];
          and_intros;
          · apply forces_s_iff hinj _ |>.not.mpr;
            grind;
          · apply forces_t_iff hinj _ |>.not.mpr;
            grind;
          · use u (3 * (i + 1));
            constructor;
            . grind;
            . exact (forces_s_iff hinj (3 * (i + 1))).mpr ⟨i + 1, rfl⟩;

/-- Every model on a frame validating `LogicFi` strongly verifies `G` (closure under
substitution is a constructor of `mkLogic`). -/
lemma stronglyVerifies_G_of_validates (hL : F ⊧ LogicFi) (V) : Model.StronglyVerifies ⟨F, V⟩ G := by
  intro σ;
  exact hL (G⟦σ⟧) (mkLogic.subst (mkLogic.addAxiom (by simp))) V

/-- **Lemma 1 of [Fin74]**: any frame validating `L` validates `∼E`. -/
theorem lemma1 (hL : F ⊧ LogicFi) : F ⊧ ∼E := by
  intro V x;
  apply forces_neg.mpr;
  by_contra hxE;
  have hE0 : x ⊩ E⟦shift 0⟧ := forces_E_subst_shift.mpr (forces_E_iff.mp hxE);
  obtain ⟨u, hu0, hu⟩ :=
    Model.exists_strictChain (P := fun m y => y ⊩ E⟦shift m⟧) hE0
      (fun m w hy => chain_step (stronglyVerifies_G_of_validates hL V) hy);
  have hR : ∀ m, u m ≺ u (m + 1) := fun m => (hu m).1;
  have hs : ∀ m, ¬(u (m + 1) ≺ u m) := fun m => (hu m).2.1;
  have hinj : Function.Injective u := Model.strictChain_injective hR hs;
  have hnH : u 0 ⊩[⟨F, (psiVal u)⟩] ∼H := psi_forces_neg_H hR hinj;
  have hH : F ⊧ H := hL H (mkLogic.addAxiom (by simp));
  have hHforces : u 0 ⊩[⟨F, (psiVal u)⟩] H := hH (psiVal u) (u 0);
  exact absurd hHforces (forces_neg.mp hnH);

end Fin74

end
