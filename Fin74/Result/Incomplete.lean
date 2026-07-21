module

public import Fin74.Logic.Basic
public import Fin74.Kripke.Chain
public import Fin74.Result.Model
public import Fin74.Result.ModelForcing
public import Fin74.Result.ValidatesG

/-! Kripke-incompleteness of Fine's logic: every frame validating `Fin74.LogicFi` validates
`∼Fin74.E`, yet `∼Fin74.E` is not itself a theorem of `Fin74.LogicFi`.

- [Fin74]
- [Lit04, p. 332] -/

@[expose]
public section

namespace Fin74

open Model.World

variable {κ : Type*} {M : Model κ ℕ} {x y : M.World} {m : ℕ}

/-- `D` persists to any successor that still forces `p₀ ⋎ p₁`. -/
lemma forces_D_of_rel (hD : x ⊩ D) (Rxy : x ≺ y) (hp : y ⊩ p0 ⋎ p1) : y ⊩ D := by
  grind [D];

/-- If `M` strongly verifies `G` and `x` forces `E⟦σ_m⟧`, then some strict successor of `x`
forces `E⟦σ_{m+1}⟧`.

- [Fin74, (3)] -/
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
  · exact forces_K_succ hK Rxy;

/-- The valuation: `s` holds exactly at chain points of index `3i`, `t` exactly at those of
index `3i+1`; all other atoms are false.

- [Fin74] -/
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
chain's origin. -/
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

variable {F : Frame κ}

/-- Every model on a frame validating `LogicFi` strongly verifies `G`. -/
lemma stronglyVerifies_G_of_validates (hL : F ⊧ LogicFi) (V) : Model.StronglyVerifies ⟨F, V⟩ G :=
  Model.stronglyVerifies_of_frame_validates (hL G (mkLogic.addAxiom (by simp))) V

/-- Any frame validating `LogicFi` validates `∼E`.

- [Fin74, Lemma 1]
- [Lit04, p. 332] -/
theorem frame_validates_neg_E_of_validates_LogicFi (hL : F ⊧ LogicFi) : F ⊧ ∼E := by
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


/-! ### Fine's logic is Kripke-incomplete -/

variable {κ : Type*} {F : Frame κ}

/-! ### Part A: propositional and `S4` axioms are valid on every reflexive-transitive frame -/

lemma validates_implyK {A B : Formula ℕ} : F ⊧ (A 🡒 B 🡒 A) := by
  intro V x; grind;

lemma validates_implyS {A B C : Formula ℕ} : F ⊧ ((A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)) := by
  intro V x; grind;

lemma validates_elimContra {A B : Formula ℕ} : F ⊧ ((∼B 🡒 ∼A) 🡒 (A 🡒 B)) := by
  intro V x; grind;

lemma validates_axiomK {A B : Formula ℕ} : F ⊧ (□(A 🡒 B) 🡒 □A 🡒 □B) := by
  intro V x; grind;

lemma validates_axiomT {A : Formula ℕ} : F ⊧ (□A 🡒 A) := by
  intro V x; grind;

lemma validates_axiom4 {A : Formula ℕ} : F ⊧ (□A 🡒 □□A) := by
  intro V x; grind;

/-! ### Part B: the concrete model strongly verifies every axiom of `LogicFi` -/

/-- Every theorem of `LogicFi` is strongly verified by Fine's model. -/
lemma stronglyVerifies_of_mkLogic {A : Formula ℕ} (h : A ∈ LogicFi) :
    fineModel.model.StronglyVerifies A := by
  induction h with
  | implyK => exact Model.stronglyVerifies_of_frame_validates validates_implyK _
  | implyS => exact Model.stronglyVerifies_of_frame_validates validates_implyS _
  | elimContra => exact Model.stronglyVerifies_of_frame_validates validates_elimContra _
  | axiomK => exact Model.stronglyVerifies_of_frame_validates validates_axiomK _
  | axiomT => exact Model.stronglyVerifies_of_frame_validates validates_axiomT _
  | axiom4 => exact Model.stronglyVerifies_of_frame_validates validates_axiom4 _
  | addAxiom hmem =>
    rcases hmem with rfl | rfl
    · exact Model.stronglyVerifies_of_frame_validates validates_G _
    · exact stronglyVerifies_H
  | mp h1 h2 ih1 ih2 =>
    intro σ x
    exact ih1 σ x (ih2 σ x)
  | nec h ih =>
    intro σ x
    rw [Formula.subst_box, forces_box]
    intro y _
    exact ih σ y
  | subst h ih =>
    rename_i τ
    intro σ x
    rw [Formula.subst_subst]
    exact ih (fun a => (τ a)⟦σ⟧) x

/-! ### Part C: `∼E` is not provable -/

lemma not_mkLogic_neg_E : ∼E ∉ LogicFi := by
  intro h
  have hSV := stronglyVerifies_of_mkLogic h
  have hEid := hSV (#·) (fineModel.World.d 0)
  rw [Formula.subst_id] at hEid
  exact absurd forces_E_d0 (forces_neg.mp hEid)

/-! ### Part D: main theorem -/

/-- Every frame validating `LogicFi` validates `∼E`, yet `∼E` is not a theorem of `LogicFi`.

- [Fin74]
- [Lit04, p. 332] -/
theorem fine_logic_kripke_incomplete :
    (∀ {κ} (F : Frame κ), F ⊧ LogicFi → F ⊧ ∼E) ∧ ∼E ∉ LogicFi :=
  ⟨fun _ hL => Fin74.frame_validates_neg_E_of_validates_LogicFi hL, not_mkLogic_neg_E⟩


end Fin74

end
