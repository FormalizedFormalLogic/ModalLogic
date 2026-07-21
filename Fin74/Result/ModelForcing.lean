module

public import Fin74.Logic.Basic
public import Fin74.Result.Model

@[expose]
public section

/-! This module shows that Fine's model (`fineModel.model`) forces `E` at `d_0`, strongly
verifies `H`, and exhibits the `b`/`c` mirror involution used to transport the mirror-image
case of the `G`-validity argument (`Fin74.Result.ValidatesG`) to the "upright" case.

- [Fin74, Lemma 2]
- [Lit04, p. 332] -/

namespace Fin74

open Model.World

/-- `B_0 = q0` is forced exactly at `b_0`. -/
lemma forces_B0_iff (w : fineModel.World) : w ⊩[fineModel.model] B 0 ↔ w = .b 0 := by
  rcases w with m|m|m|m <;> [skip; rcases m with _|_|m; skip; skip] <;>
    simp [Fin74.q0, Forces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ]

/-- `B_1 = q1` is forced exactly at `b_1`. -/
lemma forces_B1_iff (w : fineModel.World) : w ⊩[fineModel.model] B 1 ↔ w = .b 1 := by
  rcases w with m|m|m|m <;> [skip; rcases m with _|_|m; skip; skip] <;>
    simp [Fin74.q1, Forces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ]

/-- `C_0 = r0` is forced exactly at `c_0`. -/
lemma forces_C0_iff (w : fineModel.World) : w ⊩[fineModel.model] C 0 ↔ w = .c 0 := by
  rcases w with m|m|m|m <;> [skip; skip; rcases m with _|_|m; skip] <;>
    simp [Fin74.r0, Forces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ]

/-- `C_1 = r1` is forced exactly at `c_1`. -/
lemma forces_C1_iff (w : fineModel.World) : w ⊩[fineModel.model] C 1 ↔ w = .c 1 := by
  rcases w with m|m|m|m <;> [skip; skip; rcases m with _|_|m; skip] <;>
    simp [Fin74.r1, Forces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ]

/-- `B_2` is forced exactly at `b_2`. -/
lemma forces_B2_iff (w : fineModel.World) : w ⊩[fineModel.model] B 2 ↔ w = .b 2 := by
  rw [B_add_two]
  constructor
  · intro h
    obtain ⟨h12, h3⟩ := forces_and.mp h
    obtain ⟨h1, h2⟩ := forces_and.mp h12
    obtain ⟨y, hy, hfy⟩ := forces_dia.mp h1
    obtain ⟨z, hz, hfz⟩ := forces_dia.mp h2
    rw [forces_B1_iff] at hfy; subst hfy
    rw [forces_C0_iff] at hfz; subst hfz
    have h3' : ∀ y, w ≺ y → y ⊮ C 1 := not_forces_dia.mp (forces_neg.mp h3)
    cases w with
    | a m =>
      exact absurd ((forces_C1_iff (.c 1)).mpr rfl) (h3' (.c 1) (by simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame]))
    | b m =>
      have h1' : (1:ℕ) ≤ m := by simpa [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] using hy
      have h2' : (2:ℕ) ≤ m := by simpa [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] using hz
      have h3'' : ¬ (3:ℕ) ≤ m := fun hc =>
        absurd ((forces_C1_iff (.c 1)).mpr rfl) (h3' (.c 1) (by simpa [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] using hc))
      have : m = 2 := by omega
      subst this; rfl
    | c m =>
      have h1' : (3:ℕ) ≤ m := by simpa [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] using hy
      exact absurd ((forces_C1_iff (.c 1)).mpr rfl)
        (h3' (.c 1) (by simpa [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] using (by omega : (1:ℕ) ≤ m)))
    | d m =>
      exact absurd ((forces_C1_iff (.c 1)).mpr rfl) (h3' (.c 1) (by simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame]))
  · rintro rfl
    refine forces_and.mpr ⟨forces_and.mpr ⟨?_, ?_⟩, ?_⟩
    · exact forces_dia.mpr ⟨.b 1, by simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame],
        (forces_B1_iff (.b 1)).mpr rfl⟩
    · exact forces_dia.mpr ⟨.c 0, by simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame],
        (forces_C0_iff (.c 0)).mpr rfl⟩
    · refine forces_neg.mpr (not_forces_dia.mpr ?_)
      intro y hy hfy
      rw [forces_C1_iff] at hfy; subst hfy
      simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] at hy

/-- `C_2` is forced exactly at `c_2`. -/
lemma forces_C2_iff (w : fineModel.World) : w ⊩[fineModel.model] C 2 ↔ w = .c 2 := by
  rw [C_add_two]
  constructor
  · intro h
    obtain ⟨h12, h3⟩ := forces_and.mp h
    obtain ⟨h1, h2⟩ := forces_and.mp h12
    obtain ⟨y, hy, hfy⟩ := forces_dia.mp h1
    obtain ⟨z, hz, hfz⟩ := forces_dia.mp h2
    rw [forces_C1_iff] at hfy; subst hfy
    rw [forces_B0_iff] at hfz; subst hfz
    have h3' : ∀ y, w ≺ y → y ⊮ B 1 := not_forces_dia.mp (forces_neg.mp h3)
    cases w with
    | a m =>
      exact absurd ((forces_B1_iff (.b 1)).mpr rfl) (h3' (.b 1) (by simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame]))
    | c m =>
      have h1' : (1:ℕ) ≤ m := by simpa [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] using hy
      have h2' : (2:ℕ) ≤ m := by simpa [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] using hz
      have h3'' : ¬ (3:ℕ) ≤ m := fun hc =>
        absurd ((forces_B1_iff (.b 1)).mpr rfl) (h3' (.b 1) (by simpa [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] using hc))
      have : m = 2 := by omega
      subst this; rfl
    | b m =>
      have h1' : (3:ℕ) ≤ m := by simpa [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] using hy
      exact absurd ((forces_B1_iff (.b 1)).mpr rfl)
        (h3' (.b 1) (by simpa [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] using (by omega : (1:ℕ) ≤ m)))
    | d m =>
      exact absurd ((forces_B1_iff (.b 1)).mpr rfl) (h3' (.b 1) (by simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame]))
  · rintro rfl
    refine forces_and.mpr ⟨forces_and.mpr ⟨?_, ?_⟩, ?_⟩
    · exact forces_dia.mpr ⟨.c 1, by simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame],
        (forces_C1_iff (.c 1)).mpr rfl⟩
    · exact forces_dia.mpr ⟨.b 0, by simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame],
        (forces_B0_iff (.b 0)).mpr rfl⟩
    · refine forces_neg.mpr (not_forces_dia.mpr ?_)
      intro y hy hfy
      rw [forces_B1_iff] at hfy; subst hfy
      simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] at hy

/-- `d_0` forces `D`. -/
lemma forces_D_d0 : (fineModel.World.d 0) ⊩[fineModel.model] D := by
  rw [D]
  refine forces_and.mpr ⟨forces_and.mpr ⟨forces_and.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- `p0 ⋎ p1`
    exact forces_or.mpr
      (Or.inl (by simp [Forces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0]))
  · -- `□(p0 🡒 (∼p1 ⋏ ◇p1))`
    rw [forces_box]
    intro y _
    rw [forces_imp]
    match y with
    | .a m => left; simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0]
    | .b m => left; simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0]
    | .c m => left; simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0]
    | .d k =>
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · right
        refine forces_and.mpr ⟨forces_neg.mpr ?_, forces_dia.mpr ?_⟩
        · simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p1]; omega
        · refine ⟨.d (k + 1), ?_, ?_⟩
          · simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame]
          · simp [Forces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p1]; omega
      · left; simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0]; omega
  · -- `□(p1 🡒 (∼p0 ⋏ ◇p0))`
    rw [forces_box]
    intro y _
    rw [forces_imp]
    match y with
    | .a m => left; simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p1]
    | .b m => left; simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p1]
    | .c m => left; simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p1]
    | .d k =>
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · left; simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p1]; omega
      · right
        refine forces_and.mpr ⟨forces_neg.mpr ?_, forces_dia.mpr ?_⟩
        · simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0]; omega
        · refine ⟨.d (k + 1), ?_, ?_⟩
          · simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame]
          · simp [Forces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0]; omega
  · -- `□(∼(p0 ⋎ p1) 🡒 □(∼(p0 ⋎ p1)))`
    rw [forces_box]
    intro y _
    rw [forces_imp]
    match y with
    | .a m =>
      right
      rw [forces_box]
      intro z hz
      rw [forces_neg, not_forces_or]
      match z with
      | .a n => simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0, Fin74.p1]
      | .b n => simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0, Fin74.p1]
      | .c n => simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0, Fin74.p1]
      | .d n => simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] at hz
    | .b m =>
      right
      rw [forces_box]
      intro z hz
      rw [forces_neg, not_forces_or]
      match z with
      | .a n => simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0, Fin74.p1]
      | .b n => simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0, Fin74.p1]
      | .c n => simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0, Fin74.p1]
      | .d n => simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] at hz
    | .c m =>
      right
      rw [forces_box]
      intro z hz
      rw [forces_neg, not_forces_or]
      match z with
      | .a n => simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0, Fin74.p1]
      | .b n => simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0, Fin74.p1]
      | .c n => simp [Forces, NotForces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0, Fin74.p1]
      | .d n => simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] at hz
    | .d k =>
      left
      rw [not_forces_neg, forces_or]
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · exact Or.inl (by simp [Forces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p0]; omega)
      · exact Or.inr (by simp [Forces, Model.Val, fineModel.model, fineModel.frame, fineModel.φ, Fin74.p1]; omega)

/-- `A_0` is forced at `a_0`. -/
lemma forces_A0_a0 : fineModel.World.a 0 ⊩[fineModel.model] A 0 := by
  rw [A]
  refine forces_and.mpr ⟨forces_and.mpr ⟨forces_and.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact forces_dia.mpr ⟨.b 1, by simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame],
      (forces_B1_iff (.b 1)).mpr rfl⟩
  · exact forces_dia.mpr ⟨.c 1, by simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame],
      (forces_C1_iff (.c 1)).mpr rfl⟩
  · refine forces_neg.mpr (not_forces_dia.mpr ?_)
    intro y hy hfy
    rw [forces_B2_iff] at hfy; subst hfy
    simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] at hy
  · refine forces_neg.mpr (not_forces_dia.mpr ?_)
    intro y hy hfy
    rw [forces_C2_iff] at hfy; subst hfy
    simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] at hy

/-- `◇(A_0)` is forced at `d_0`. -/
lemma forces_dia_A0_d0 : fineModel.World.d 0 ⊩[fineModel.model] ◇(A 0) :=
  forces_dia.mpr ⟨.a 0, by simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame], forces_A0_a0⟩

/-- `d_0` forces `K 0` (the block `K1 0 ⋏ K2 0 ⋏ K3 0 ⋏ K4 0`). -/
lemma forces_K0_at_d0 : (fineModel.World.d 0 : fineModel.World) ⊩[fineModel.model] K 0 := by
  simp only [K, forces_and]
  and_intros
  · -- K1 0 : □(B 1 → ◇B 0 ∧ ∼◇C 0)
    rw [K1, forces_box]
    intro y _ hy
    rw [forces_B1_iff] at hy; subst hy
    refine forces_and.mpr ⟨?_, ?_⟩
    · exact forces_dia.mpr ⟨.b 0, by simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame],
        (forces_B0_iff (.b 0)).mpr rfl⟩
    · refine forces_neg.mpr (not_forces_dia.mpr ?_)
      intro z hz hzC0
      rw [forces_C0_iff] at hzC0; subst hzC0
      simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] at hz
  · -- K2 0 : □(C 1 → ◇C 0 ∧ ∼◇B 0)
    rw [K2, forces_box];
    intro y _ hy
    rw [forces_C1_iff] at hy; subst hy
    refine forces_and.mpr ⟨?_, ?_⟩
    · exact forces_dia.mpr ⟨.c 0, by simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame],
        (forces_C0_iff (.c 0)).mpr rfl⟩
    · refine forces_neg.mpr (not_forces_dia.mpr ?_)
      intro z hz hzB0
      rw [forces_B0_iff] at hzB0; subst hzB0
      simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] at hz
  · -- K3 0 : □(B 0 → ∼◇B 1)
    rw [K3, forces_box]
    intro y _ hy
    rw [forces_B0_iff] at hy; subst hy
    refine forces_neg.mpr (not_forces_dia.mpr ?_)
    intro z hz hzB1
    rw [forces_B1_iff] at hzB1; subst hzB1
    simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] at hz
  · -- K4 0 : □(C 0 → ∼◇C 1)
    rw [K4, forces_box]
    intro y _ hy;
    rw [forces_C0_iff] at hy; subst hy;
    apply not_forces_dia.mpr;
    intro z hz hzC1
    rw [forces_C1_iff] at hzC1; subst hzC1;
    simp [Frame.Rel, fineModel.R, fineModel.model, fineModel.frame] at hz

/-- `d_0` forces `E`. -/
lemma forces_E_d0 : (fineModel.World.d 0) ⊩[fineModel.model] E :=
  forces_E_iff.mpr ⟨forces_D_d0, forces_dia_A0_d0, forces_K0_at_d0⟩

/-! ### Fine's model strongly verifies `H` -/

/-- A shrinking-domain existential `∃ k ≥ i, P k` is eventually constant in `i`. -/
private lemma exists_ge_eventually_const (P : ℕ → Prop) :
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → ((∃ k, i ≤ k ∧ P k) ↔ (∃ k, j ≤ k ∧ P k)) := by
  by_cases h : ∀ B : ℕ, ∃ k, B ≤ k ∧ P k;
  · use 0;
    intro i j _ _;
    exact ⟨fun _ => h j, fun _ => h i⟩;
  · push Not at h;
    obtain ⟨B, hB⟩ := h;
    use B;
    intro i j hi hj;
    constructor;
    · rintro ⟨k, hik, hPk⟩;
      exact absurd hPk (hB k (le_trans hi hik));
    · rintro ⟨k, hjk, hPk⟩;
      exact absurd hPk (hB k (le_trans hj hjk));

/-- Along the `d`-chain, the truth of any fixed formula `C` is *eventually periodic with
period (dividing) 2*: past some threshold `N`, `d_i ⊩ C` depends only on the parity of `i`.

- [Fin74, p.\ 28]
-/
lemma d_eventually_period_two (C : Formula ℕ) :
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → i % 2 = j % 2 →
      ((fineModel.World.d i ⊩[fineModel.model] C) ↔ (fineModel.World.d j ⊩[fineModel.model] C)) := by
  induction C with
  | atom a =>
    use 0;
    intro i j _ _ hij;
    cases a with
    | zero => simp [Forces, Model.Val, fineModel.model, fineModel.φ, hij];
    | succ a =>
      cases a with
      | zero => simp [Forces, Model.Val, fineModel.model, fineModel.φ, hij];
      | succ a => simp [Forces, Model.Val, fineModel.model, fineModel.φ];
  | bot =>
    use 0;
    intro i j _ _ _;
    simp [Forces];
  | imp A B ihA ihB =>
    obtain ⟨NA, hNA⟩ := ihA;
    obtain ⟨NB, hNB⟩ := ihB;
    use max NA NB;
    intro i j hi hj hij;
    have hiA := le_trans (le_max_left NA NB) hi;
    have hjA := le_trans (le_max_left NA NB) hj;
    have hiB := le_trans (le_max_right NA NB) hi;
    have hjB := le_trans (le_max_right NA NB) hj;
    simp only [forces_imp, NotForces, hNA i j hiA hjA hij, hNB i j hiB hjB hij];
  | dia A ih =>
    -- `d_i ⊩ ◇A` decomposes into the (index-independent) truth of `A` among `b`/`c` points and
    -- two existentials `∃ k ≥ i, …` over the `d`- and `a`-cones of `d_i`, each antitone in `i`
    -- and hence eventually constant.
    have hdia : ∀ i : ℕ, (fineModel.World.d i ⊩[fineModel.model] ◇A) ↔
        (∃ k, i ≤ k ∧ (fineModel.World.d k ⊩[fineModel.model] A)) ∨ (∃ m, i ≤ m ∧ (fineModel.World.a m ⊩[fineModel.model] A)) ∨
        (∃ k, (fineModel.World.b k ⊩[fineModel.model] A)) ∨ (∃ k, (fineModel.World.c k ⊩[fineModel.model] A)) := by
      intro i;
      rw [forces_dia];
      constructor;
      · rintro ⟨y, hy, hyA⟩;
        cases y with
        | d k => exact Or.inl ⟨k, hy, hyA⟩;
        | a m => exact Or.inr (Or.inl ⟨m, hy, hyA⟩);
        | b k => exact Or.inr (Or.inr (Or.inl ⟨k, hyA⟩));
        | c k => exact Or.inr (Or.inr (Or.inr ⟨k, hyA⟩));
      · rintro (⟨k, hk, hA⟩ | ⟨m, hm, hA⟩ | ⟨k, hA⟩ | ⟨k, hA⟩);
        · exact ⟨fineModel.World.d k, hk, hA⟩;
        · exact ⟨fineModel.World.a m, hm, hA⟩;
        · exact ⟨fineModel.World.b k, trivial, hA⟩;
        · exact ⟨fineModel.World.c k, trivial, hA⟩;
    obtain ⟨N1, hN1⟩ := exists_ge_eventually_const (fun k => fineModel.World.d k ⊩[fineModel.model] A);
    obtain ⟨N2, hN2⟩ := exists_ge_eventually_const (fun m => fineModel.World.a m ⊩[fineModel.model] A);
    use max N1 N2;
    intro i j hi hj _hij;
    have hi1 := le_trans (le_max_left N1 N2) hi;
    have hj1 := le_trans (le_max_left N1 N2) hj;
    have hi2 := le_trans (le_max_right N1 N2) hi;
    have hj2 := le_trans (le_max_right N1 N2) hj;
    rw [hdia i, hdia j, hN1 i j hi1 hj1, hN2 i j hi2 hj2];

open Fin74 (H s t)

/-- The three pairwise-incompatible phases that a refutation point of `H` cycles through under a
substitution `σ`. -/
def phase (σ : Formula.Substitution ℕ ℕ) (r : ℕ) : Formula ℕ :=
  match r with
  | 0 => s⟦σ⟧
  | 1 => ∼(s⟦σ⟧) ⋏ t⟦σ⟧
  | _ => ∼(s⟦σ⟧) ⋏ ∼(t⟦σ⟧)

@[simp, grind =] lemma phase_zero (σ : Formula.Substitution ℕ ℕ) : phase σ 0 = s⟦σ⟧ := rfl
@[simp, grind =] lemma phase_one (σ : Formula.Substitution ℕ ℕ) :
    phase σ 1 = ∼(s⟦σ⟧) ⋏ t⟦σ⟧ := rfl
@[simp, grind =] lemma phase_add_two (σ : Formula.Substitution ℕ ℕ) (r : ℕ) :
    phase σ (r + 2) = ∼(s⟦σ⟧) ⋏ ∼(t⟦σ⟧) := rfl

/-- No world forces two distinct phases (among residues `< 3`) at once. -/
private lemma phase_incompatible {σ : Formula.Substitution ℕ ℕ} {w : fineModel.World} {i j : ℕ}
    (hi3 : i < 3) (hj3 : j < 3) (hij : i ≠ j)
    (hi : w ⊩[fineModel.model] phase σ i) (hj : w ⊩[fineModel.model] phase σ j) : False := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega;
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega;
  rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;> simp_all <;> grind;

/-- Auxiliary formula along the phase chain, bundling the current phase with the `◇`-witness
needed to advance to the next phase. -/
private def Y (σ : Formula.Substitution ℕ ℕ) (m : ℕ) : Formula ℕ :=
  match m % 3 with
  | 0 => phase σ 0
  | 1 => phase σ 1 ⋏ ◇(phase σ 2 ⋏ ◇(phase σ 0))
  | _ => phase σ 2 ⋏ ◇(phase σ 0)

private lemma Y_imp_phase {σ : Formula.Substitution ℕ ℕ} {w : fineModel.World} {m : ℕ} (h : w ⊩[fineModel.model] Y σ m) :
    w ⊩[fineModel.model] phase σ (m % 3) := by
  unfold Y at h;
  have h3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega;
  rcases h3 with h' | h' | h' <;> simp only [h'] at h ⊢ <;> [exact h; exact (forces_and.mp h).1;
    exact (forces_and.mp h).1];

/-- One step of the phase chain: `H`'s box hypothesis `hbox` at `x` produces, from `w` forcing
`Y σ m` (with `x ≺ w`), a strict successor `v` forcing `Y σ (m + 1)`. -/
private lemma Y_step {σ : Formula.Substitution ℕ ℕ} {x : fineModel.World}
    (hbox : x ⊩[fineModel.model] □(phase σ 0 🡒 ◇(Y σ 1))) (m : ℕ) {w : fineModel.World}
    (hxw : fineModel.R x w) (hw : w ⊩[fineModel.model] Y σ m) :
    ∃ v, fineModel.R w v ∧ ¬ fineModel.R v w ∧ fineModel.R x v ∧ v ⊩[fineModel.model] Y σ (m + 1) := by
  have h3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega;
  obtain ⟨v, hwv, hv⟩ : ∃ v, fineModel.R w v ∧ v ⊩[fineModel.model] Y σ (m + 1) := by
    rcases h3 with h0 | h1 | h2;
    · have hYm : Y σ m = phase σ 0 := by unfold Y; rw [h0]; rfl;
      have h1 : (m + 1) % 3 = 1 := by omega;
      have hYm1 : Y σ (m + 1) = phase σ 1 ⋏ ◇(phase σ 2 ⋏ ◇(phase σ 0)) := by unfold Y; rw [h1]; rfl;
      rw [hYm] at hw;
      rw [hYm1];
      have hwψ := forces_box.mp hbox w hxw;
      have hdia : w ⊩[fineModel.model] ◇(phase σ 1 ⋏ ◇(phase σ 2 ⋏ ◇(phase σ 0))) :=
        (forces_imp.mp hwψ).resolve_left (fun hcon => hcon hw);
      exact forces_dia.mp hdia;
    · have hYm : Y σ m = phase σ 1 ⋏ ◇(phase σ 2 ⋏ ◇(phase σ 0)) := by unfold Y; rw [h1]; rfl;
      have h2 : (m + 1) % 3 = 2 := by omega;
      have hYm1 : Y σ (m + 1) = phase σ 2 ⋏ ◇(phase σ 0) := by unfold Y; rw [h2]; rfl;
      rw [hYm] at hw;
      rw [hYm1];
      exact forces_dia.mp (forces_and.mp hw).2;
    · have hYm : Y σ m = phase σ 2 ⋏ ◇(phase σ 0) := by unfold Y; rw [h2]; rfl;
      have h0 : (m + 1) % 3 = 0 := by omega;
      have hYm1 : Y σ (m + 1) = phase σ 0 := by unfold Y; rw [h0]; rfl;
      rw [hYm] at hw;
      rw [hYm1];
      exact forces_dia.mp (forces_and.mp hw).2;
  have hxv : fineModel.R x v := fineModel.R_trans hxw hwv;
  refine ⟨v, hwv, ?_, hxv, hv⟩;
  intro hvw;
  have heq : v = w := fineModel.R_antisymm hvw hwv;
  rw [heq] at hv;
  exact phase_incompatible (Nat.mod_lt m (by omega)) (Nat.mod_lt (m + 1) (by omega))
    (by omega) (Y_imp_phase hw) (Y_imp_phase hv);

/-- If Fine's model does not strongly verify `H`, some refutation point `x` of `H⟦σ⟧` starts an
infinite *strict* chain along `fineModel.R` whose points cycle through the three
pairwise-incompatible phases `phase σ 0`, `phase σ 1`, `phase σ 2` in order.

- [Fin74, p.\ 28]
-/
lemma exists_phase_chain (h : ∃ σ x, x ⊮[fineModel.model] H⟦σ⟧) :
    ∃ (σ : Formula.Substitution ℕ ℕ) (u : ℕ → fineModel.World),
      (∀ m, fineModel.R (u m) (u (m + 1))) ∧ (∀ m, ¬ fineModel.R (u (m + 1)) (u m)) ∧
      ∀ m, u m ⊩[fineModel.model] phase σ (m % 3) := by
  obtain ⟨σ, x, hx⟩ := h;
  have hx' : x ⊩[fineModel.model] phase σ 0 ⋏ □(phase σ 0 🡒 ◇(Y σ 1)) := not_forces_neg.mp hx;
  obtain ⟨hxs, hbox⟩ := forces_and.mp hx';
  have h0 : fineModel.R x x ∧ x ⊩[fineModel.model] Y σ 0 := ⟨fineModel.R_refl x, hxs⟩;
  obtain ⟨u, hu0, hu⟩ := Model.exists_strictChain (P := fun m w => fineModel.R x w ∧ w ⊩[fineModel.model] Y σ m) h0
    (fun m w hw => Y_step hbox m hw.1 hw.2);
  refine ⟨σ, u, fun m => (hu m).1, fun m => (hu m).2.1, fun m => Y_imp_phase (hu m).2.2.2⟩;

/-- Among any three natural numbers, two are congruent mod 2 (pigeonhole on the two parity
classes). -/
@[grind =>]
lemma exists_same_parity_triple (a b c : ℕ) : (a % 2 = b % 2) ∨ (a % 2 = c % 2) ∨ (b % 2 = c % 2) := by
  omega

/-- Among the three consecutive-block indices `3*j`, `3*j+1`, `3*j+2`, some two distinct ones
`i₁ < i₂` land on values `k i₁`, `k i₂` that are congruent mod 2. -/
lemma exists_same_parity_pair (k : ℕ → ℕ) (j : ℕ) :
    ∃ i₁ i₂, i₁ < i₂ ∧ i₁ ∈ ({3 * j, 3 * j + 1, 3 * j + 2} : Set ℕ) ∧
      i₂ ∈ ({3 * j, 3 * j + 1, 3 * j + 2} : Set ℕ) ∧ k i₁ % 2 = k i₂ % 2 := by
  rcases exists_same_parity_triple (k (3 * j)) (k (3 * j + 1)) (k (3 * j + 2)) with h | h | h;
  · use 3 * j, 3 * j + 1;
    grind;
  · use 3 * j, 3 * j + 2;
    grind;
  · use 3 * j + 1, 3 * j + 2;
    grind;

/-- Fine's model strongly verifies `H`.

- [Fin74, p.\ 28]
-/
theorem stronglyVerifies_H : fineModel.model.StronglyVerifies H := by
  -- If some substitution instance `H⟦σ⟧` were refuted, `exists_phase_chain` would produce an
  -- infinite strict `fineModel.R`-chain cycling through the three pairwise-incompatible phases;
  -- `fineModel.strict_chain_all_d` confines it to the `d`-points at strictly increasing indices
  -- `k`, and `d_eventually_period_two` makes each phase's truth along the `d`-chain eventually
  -- depend only on parity. Pigeonholing three consecutive indices among two parities
  -- (`exists_same_parity_pair`) then forces two different phases to coincide at the same
  -- `d`-point, contradicting `phase_incompatible`.
  by_contra hcon;
  unfold Model.StronglyVerifies Model.Validates at hcon;
  push Not at hcon;
  obtain ⟨σ, x, hx⟩ := hcon;
  obtain ⟨σ, u, hR, hs, hphase⟩ := exists_phase_chain ⟨σ, x, hx⟩;
  choose k hk using fun i => fineModel.strict_chain_all_d hR hs i;
  have hkmono : StrictMono k := by
    apply strictMono_nat_of_lt_succ;
    intro m;
    have hR' : fineModel.R (u m) (u (m + 1)) := hR m;
    have hs' : ¬ fineModel.R (u (m + 1)) (u m) := hs m;
    rw [hk m, hk (m + 1)] at hR' hs';
    simp only [fineModel.R] at hR' hs';
    omega;
  have hkge : ∀ m, m ≤ k m := fun m => hkmono.le_apply;
  obtain ⟨N0, hN0⟩ := d_eventually_period_two (phase σ 0);
  obtain ⟨N1, hN1⟩ := d_eventually_period_two (phase σ 1);
  obtain ⟨N2, hN2⟩ := d_eventually_period_two (phase σ 2);
  set N := max N0 (max N1 N2) with hN;
  have hN0le : N0 ≤ N := le_max_left _ _;
  have hN1le : N1 ≤ N := le_trans (le_max_left _ _) (le_max_right _ _);
  have hN2le : N2 ≤ N := le_trans (le_max_right _ _) (le_max_right _ _);
  obtain ⟨i₁, i₂, hi12, hi1mem, hi2mem, hpar⟩ := exists_same_parity_pair k N;
  have hi1mem' : i₁ = 3 * N ∨ i₁ = 3 * N + 1 ∨ i₁ = 3 * N + 2 := by simpa using hi1mem;
  have hi2mem' : i₂ = 3 * N ∨ i₂ = 3 * N + 1 ∨ i₂ = 3 * N + 2 := by simpa using hi2mem;
  have hi1ne2 : i₁ % 3 ≠ i₂ % 3 := by omega;
  have hi1lt3 : i₁ % 3 < 3 := by omega;
  have hi2lt3 : i₂ % 3 < 3 := by omega;
  have hki1N : N ≤ k i₁ := le_trans (by omega) (hkge i₁);
  have hki2N : N ≤ k i₂ := le_trans (by omega) (hkge i₂);
  have hu1 : u i₁ ⊩[fineModel.model] phase σ (i₁ % 3) := hphase i₁;
  have hu2 : u i₂ ⊩[fineModel.model] phase σ (i₂ % 3) := hphase i₂;
  rw [hk i₁] at hu1;
  rw [hk i₂] at hu2;
  have hi1mod3 : i₁ % 3 = 0 ∨ i₁ % 3 = 1 ∨ i₁ % 3 = 2 := by omega;
  have htransfer : fineModel.World.d (k i₂) ⊩[fineModel.model] phase σ (i₁ % 3) := by
    rcases hi1mod3 with h0 | h1 | h2;
    · rw [h0] at hu1 ⊢;
      rw [← hN0 (k i₁) (k i₂) (le_trans hN0le hki1N) (le_trans hN0le hki2N) hpar];
      exact hu1;
    · rw [h1] at hu1 ⊢;
      rw [← hN1 (k i₁) (k i₂) (le_trans hN1le hki1N) (le_trans hN1le hki2N) hpar];
      exact hu1;
    · rw [h2] at hu1 ⊢;
      rw [← hN2 (k i₁) (k i₂) (le_trans hN2le hki1N) (le_trans hN2le hki2N) hpar];
      exact hu1;
  exact phase_incompatible hi1lt3 hi2lt3 hi1ne2 htransfer hu2;

/-! ### The `b`/`c` mirror involution

Since the corrected formula family is genuinely symmetric under exchanging `B`-related
atoms with `C`-related atoms, an analysis carried out at a `c`-heavy point of Fine's model
can be transported to the mirror `b`-heavy point for free via the involution `swap` on
worlds (exchanging the `b`/`c` families) together with the atom substitution `tau`
(exchanging the atoms underlying `B` and `C`). -/


/-- The involution on Fine's model's worlds exchanging the `b`- and `c`-families and fixing
the `a`- and `d`-families. -/
def swap : fineModel.World → fineModel.World
| .a m => .a m
| .b m => .c m
| .c m => .b m
| .d m => .d m

lemma swap_involutive : Function.Involutive swap := by
  intro x; cases x <;> rfl

/-- Fine's model's accessibility relation `fineModel.R` does not distinguish the `b`- and
`c`-families, only their indices. -/
lemma R_swap {x y : fineModel.World} : fineModel.R (swap x) (swap y) ↔ fineModel.R x y := by
  cases x <;> cases y <;> simp [fineModel.R, swap]



/-- The atom substitution exchanging the atoms underlying `B` (`q0`/`q1`) with those
underlying `C` (`r0`/`r1`), fixing every other atom. -/
def tau : Formula.Substitution ℕ ℕ
| 2 => r0
| 3 => r1
| 4 => q0
| 5 => q1
| a => #a

@[simp, grind =] lemma tau_p0 : p0⟦tau⟧ = p0 := rfl
@[simp, grind =] lemma tau_p1 : p1⟦tau⟧ = p1 := rfl
@[simp, grind =] lemma tau_q0 : q0⟦tau⟧ = r0 := rfl
@[simp, grind =] lemma tau_q1 : q1⟦tau⟧ = r1 := rfl
@[simp, grind =] lemma tau_r0 : r0⟦tau⟧ = q0 := rfl
@[simp, grind =] lemma tau_r1 : r1⟦tau⟧ = q1 := rfl
@[simp, grind =] lemma tau_s : s⟦tau⟧ = s := rfl
@[simp, grind =] lemma tau_t : t⟦tau⟧ = t := rfl

/-- Substituting `tau` exchanges `B` and `C` at every index. -/
lemma B_C_subst_tau (n : ℕ) : (B n)⟦tau⟧ = C n ∧ (C n)⟦tau⟧ = B n :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    obtain ⟨ihB1, ihC1⟩ := B_C_subst_tau (n + 1);
    obtain ⟨ihB0, ihC0⟩ := B_C_subst_tau n;
    constructor;
    . simp_all;
    . simp_all;

lemma B_subst_tau (n : ℕ) : (B n)⟦tau⟧ = C n := (B_C_subst_tau n).1
lemma C_subst_tau (n : ℕ) : (C n)⟦tau⟧ = B n := (B_C_subst_tau n).2

/-- Forcing is invariant under simultaneously permuting the points of Fine's model by `swap`
and permuting the valuation along `swap`. -/
lemma forces_swap_iff {ψ : fineModel.World → ℕ → Prop} {x : fineModel.World} {X : Formula ℕ} :
    x ⊩[⟨fineModel.frame, ψ⟩] X ↔ swap x ⊩[⟨fineModel.frame, ψ ∘ swap⟩] X := by
  induction X generalizing x with
  | atom a => simp [Model.World.Forces, Model.Val, Function.comp, swap_involutive x]
  | bot => simp [Model.World.Forces]
  | imp A B ihA ihB => simp [Model.World.Forces, ihA, ihB]
  | dia A ih =>
    simp only [Model.World.Forces];
    constructor;
    . rintro ⟨y, hxy, hy⟩; exact ⟨swap y, R_swap.mpr hxy, ih.mp hy⟩;
    . rintro ⟨y, hxy, hy⟩;
      refine ⟨swap y, ?_, ?_⟩;
      . exact R_swap.mp (by rwa [swap_involutive y]);
      . exact ih.mpr (by rwa [swap_involutive y])


end Fin74

end
