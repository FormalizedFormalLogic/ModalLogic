module

public import Fin74.Logic.Shift
public import Fin74.Kripke.Chain

@[expose]
public section

namespace Fin74

variable {κ : Type*} {M : Model κ ℕ} {x y : M.World} {m : ℕ}

/-- `K1` climbs one level, by projection from the unfolding of `B (m+2)`: no hypotheses are
needed. -/
lemma forces_K1_succ : x ⊩ K1 (m + 1) := by
  dsimp [K1];
  grind;

/-- The repair of the flawed auxiliary result (2) of [Fin74]: the paper's argument for `K2`
one level up is unsound in general (see the falsifying model recorded alongside this plan),
but it follows from the witness's `∼◇(A m)` obtained in the chain step instead. -/
lemma forces_K2_succ_of_not_dia_A (hA : x ⊩ ∼◇(A m)) : x ⊩ K2 (m + 1) := by
  rw [K2, Model.World.forces_box];
  intro y hxy hy;
  rw [C_add_two] at hy;
  simp only [Model.World.forces_and] at hy;
  rw [Model.World.forces_and];
  refine ⟨hy.1.1, ?_⟩;
  rw [Model.World.forces_neg];
  intro hcon;
  have hAy : y ⊩ A m := by
    rw [A];
    simp only [Model.World.forces_and];
    exact ⟨⟨hcon, hy.1.1⟩, hy.2⟩;
  exact hA ⟨y, hxy, hAy⟩;

/-- `K3` climbs one level, from `K1` at the current level and transitivity. -/
lemma forces_K3_succ_of_K1 (h1 : x ⊩ K1 m) (hxy : x ≺ y) : y ⊩ K3 (m + 1) := by
  rw [K1, Model.World.forces_box] at h1;
  rw [K3, Model.World.forces_box];
  intro z hyz hz;
  have hxz : x ≺ z := Model.rel_trans' hxy hyz;
  have h1z := h1 z hxz hz;
  rw [Model.World.forces_and] at h1z;
  rw [Model.World.forces_neg];
  intro hcon;
  obtain ⟨u, hzu, hu⟩ := hcon;
  rw [B_add_two] at hu;
  simp only [Model.World.forces_and] at hu;
  exact h1z.2 (Model.World.forces_dia_of_rel hu.1.2 hzu);

/-- `K4` climbs one level, from `K2` at the current level and transitivity. -/
lemma forces_K4_succ_of_K2 (h2 : x ⊩ K2 m) (hxy : x ≺ y) : y ⊩ K4 (m + 1) := by
  rw [K2, Model.World.forces_box] at h2;
  rw [K4, Model.World.forces_box];
  intro z hyz hz;
  have hxz : x ≺ z := Model.rel_trans' hxy hyz;
  have h2z := h2 z hxz hz;
  rw [Model.World.forces_and] at h2z;
  rw [Model.World.forces_neg];
  intro hcon;
  obtain ⟨u, hzu, hu⟩ := hcon;
  rw [C_add_two] at hu;
  simp only [Model.World.forces_and] at hu;
  exact h2z.2 (Model.World.forces_dia_of_rel hu.1.2 hzu);

/-- The whole `K`-block climbs one level along a chain step, given the successor's
`∼◇(A m)`. -/
lemma forces_K_succ (hK : x ⊩ K m) (hxy : x ≺ y) (hA : y ⊩ ∼◇(A m)) : y ⊩ K (m + 1) := by
  simp only [K] at hK ⊢;
  grind [forces_K1_succ, forces_K2_succ_of_not_dia_A, forces_K3_succ_of_K1, forces_K4_succ_of_K2];

/-- `D` persists to any successor that still forces `p₀ ⋎ p₁` (its two boxed conjuncts
persist along any accessible world). -/
lemma forces_D_of_rel (hD : x ⊩ D) (hxy : x ≺ y) (hp : y ⊩ p0 ⋎ p1) : y ⊩ D := by
  simp only [D] at hD ⊢;
  grind [Model.World.forces_box_of_rel];

/-- Auxiliary result (3) of [Fin74], repaired: if `M` strongly verifies `G` and `x` forces
`E⟦σ_m⟧`, then some strict successor of `x` forces `E⟦σ_{m+1}⟧`. -/
lemma chain_step (hG : M.StronglyVerifies G) (hx : x ⊩ E⟦shift m⟧) :
    ∃ y : M.World, x ≺ y ∧ ¬(y ≺ x) ∧ y ⊩ E⟦shift (m + 1)⟧ := by
  have hxF : x ⊩ F⟦shift m⟧ := hG (shift m) x hx;
  obtain ⟨y, hxy, hy01, hyA, hyA'⟩ := forces_F_subst_shift.mp hxF;
  obtain ⟨hD, hAm, hK⟩ := forces_E_subst_shift.mp hx;
  have hstrict : ¬(y ≺ x) := by
    intro hyx;
    exact hyA (Model.World.forces_dia_of_rel hAm hyx);
  refine ⟨y, hxy, hstrict, forces_E_subst_shift.mpr ?_⟩;
  and_intros;
  · exact forces_D_of_rel hD hxy hy01;
  · exact hyA';
  · exact forces_K_succ hK hxy hyA;

variable {u : ℕ → κ}

/-- The valuation `ψ` of [Fin74]: `s` holds exactly at chain points of index `3i`, `t`
exactly at those of index `3i+1`. Only the atoms `s` (`#6`) and `t` (`#7`) matter; all other
atoms are false. -/
def psiVal (u : ℕ → κ) : κ → ℕ → Prop
| v, 6 => ∃ i, v = u (3 * i)
| v, 7 => ∃ i, v = u (3 * i + 1)
| _, _ => False

variable {F : Frame κ}

/-- `s` holds exactly at chain points of index a multiple of `3`, on the ψ-model over an
injective chain `u`. -/
lemma forces_s_iff (hinj : Function.Injective u) (n : ℕ) :
    u n ⊩[F.model (psiVal u)] s ↔ ∃ i, n = 3 * i := by
  rw [s, show (u n ⊩[F.model (psiVal u)] (#6 : Formula ℕ)) = psiVal u (u n) 6 from rfl];
  constructor;
  · rintro ⟨i, hi⟩; exact ⟨i, hinj hi⟩;
  · rintro ⟨i, hi⟩; exact ⟨i, by rw [hi]⟩;

/-- `t` holds exactly at chain points of index `1` more than a multiple of `3`, on the
ψ-model over an injective chain `u`. -/
lemma forces_t_iff (hinj : Function.Injective u) (n : ℕ) :
    u n ⊩[F.model (psiVal u)] t ↔ ∃ i, n = 3 * i + 1 := by
  rw [t, show (u n ⊩[F.model (psiVal u)] (#7 : Formula ℕ)) = psiVal u (u n) 7 from rfl];
  constructor;
  · rintro ⟨i, hi⟩; exact ⟨i, hinj hi⟩;
  · rintro ⟨i, hi⟩; exact ⟨i, by rw [hi]⟩;

/-- On the ψ-model over any injective ascending chain along `F`, `∼H` is forced at the
chain's origin. Injectivity is essential: it lets the three phases `s`, `¬s ∧ t`, `¬s ∧ ¬t`
be told apart along the chain by their index mod 3. -/
lemma psi_forces_neg_H (hR : ∀ m, F.Rel' (u m) (u (m + 1)))
    (hinj : Function.Injective u) :
    u 0 ⊩[F.model (psiVal u)] ∼H := by
  rw [Model.World.forces_neg];
  unfold H;
  rw [Model.World.not_forces_neg, Model.World.forces_and];
  and_intros;
  · exact (forces_s_iff hinj 0).mpr ⟨0, rfl⟩;
  · rw [Model.World.forces_box];
    intro y hy hys;
    obtain ⟨i, hi⟩ := hys;
    subst hi;
    have h01 : F.Rel' (u (3 * i)) (u (3 * i + 1)) := hR (3 * i);
    use u (3 * i + 1), h01;
    simp only [Model.World.forces_and];
    and_intros;
    · rw [Model.World.forces_neg];
      intro hcontra;
      obtain ⟨j, hj⟩ := (forces_s_iff hinj _).mp hcontra;
      omega;
    · exact (forces_t_iff hinj (3 * i + 1)).mpr ⟨i, rfl⟩;
    · have h12 : F.Rel' (u (3 * i + 1)) (u (3 * i + 2)) := by
        have := hR (3 * i + 1);
        have e : 3 * i + 1 + 1 = 3 * i + 2 := by omega;
        rwa [e] at this;
      have h23 : F.Rel' (u (3 * i + 2)) (u (3 * (i + 1))) := by
        have := hR (3 * i + 2);
        have e : 3 * i + 2 + 1 = 3 * (i + 1) := by omega;
        rwa [e] at this;
      use u (3 * i + 2), h12;
      simp only [Model.World.forces_and];
      and_intros;
      · rw [Model.World.forces_neg];
        intro hcontra;
        obtain ⟨j, hj⟩ := (forces_s_iff hinj _).mp hcontra;
        omega;
      · rw [Model.World.forces_neg];
        intro hcontra;
        obtain ⟨j, hj⟩ := (forces_t_iff hinj _).mp hcontra;
        omega;
      · exact ⟨u (3 * (i + 1)), h23, (forces_s_iff hinj (3 * (i + 1))).mpr ⟨i + 1, rfl⟩⟩;

/-- Every model on a frame validating `LogicFi` strongly verifies `G` (closure under
substitution is a constructor of `mkLogic`). -/
lemma stronglyVerifies_G_of_validates (hL : F ⊧ LogicFi) (V) : Model.StronglyVerifies ⟨F, V⟩ G := by
  intro σ;
  exact hL (G⟦σ⟧) (mkLogic.subst (mkLogic.addAxiom (by simp))) V

/-- **Lemma 1 of [Fin74]**: any frame validating `L` validates `∼E`. -/
theorem lemma1 (hL : F ⊧ LogicFi) : F.Validates (∼E) := by
  intro V x;
  rw [Model.World.forces_neg];
  intro hxE;
  have hE0 : x ⊩ E⟦shift 0⟧ := forces_E_subst_shift.mpr (forces_E_iff.mp hxE);
  obtain ⟨u, hu0, hu⟩ :=
    Model.exists_strictChain (P := fun m y => y ⊩ E⟦shift m⟧) hE0
      (fun m w hy => chain_step (stronglyVerifies_G_of_validates hL V) hy);
  have hR : ∀ m, u m ≺ u (m + 1) := fun m => (hu m).1;
  have hs : ∀ m, ¬(u (m + 1) ≺ u m) := fun m => (hu m).2.1;
  have hinj : Function.Injective u := Model.strictChain_injective hR hs;
  have hnH : u 0 ⊩[F.model (psiVal u)] ∼H := psi_forces_neg_H (F := F) hR hinj;
  have hH : F.Validates H := hL H (mkLogic.addAxiom (by simp));
  have hHforces : u 0 ⊩[F.model (psiVal u)] H := hH (psiVal u) (u 0);
  exact absurd hHforces (Model.World.forces_neg.mp hnH);

end Fin74

end
