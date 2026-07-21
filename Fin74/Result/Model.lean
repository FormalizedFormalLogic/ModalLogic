module

public import Fin74.Kripke.Basic
public import Fin74.Kripke.Chain
public import Fin74.Logic.Basic

@[expose]
public section

namespace Fin74

/-! The concrete countermodel `𝔄 = (fineModel.World, fineModel.R, fineModel.φ)` from [Fin74]
witnessing `∼E ∉ L` (Lemma 2), commonly known as *Fine's model*. Definitions and lemmas about it
live under the `fineModel` namespace and are always accessed with the `fineModel.` prefix, since
they only make sense for this one specific model. -/

namespace fineModel

protected inductive World
| a (m : ℕ)
| b (m : ℕ)
| c (m : ℕ)
| d (m : ℕ)
deriving DecidableEq

/-- The accessibility relation of Fine's model, given in closed form (no transitive closure),
reconstructed from [Fin74]'s (partly missing) definition. -/
@[grind =]
protected def R : fineModel.World → fineModel.World → Prop
| .b m, .b k => k ≤ m
| .b m, .c k => k + 2 ≤ m
| .c m, .c k => k ≤ m
| .c m, .b k => k + 2 ≤ m
| .a m, .a k => k = m
| .a m, .b k => k ≤ m + 1
| .a m, .c k => k ≤ m + 1
| .d n, .d k => n ≤ k
| .d n, .a m => n ≤ m
| .d _, .b _ => True
| .d _, .c _ => True
| _, _ => False

@[grind .] protected lemma R_refl (w : fineModel.World) : fineModel.R w w := by cases w <;> simp [fineModel.R]

@[grind →]
protected lemma R_trans {x y z : fineModel.World} (hxy : fineModel.R x y) (hyz : fineModel.R y z) : fineModel.R x z := by
  cases x <;> cases y <;> cases z <;> simp_all [fineModel.R] <;> omega

/-- `fineModel.R` is antisymmetric, so `(fineModel.World, fineModel.R)` is a partial order. -/
protected lemma R_antisymm {x y : fineModel.World} (hxy : fineModel.R x y) (hyx : fineModel.R y x) : x = y := by
  cases x <;> cases y <;> simp_all [fineModel.R] <;> omega

protected def frame : Frame fineModel.World where
  Rel' := fineModel.R
  rel_refl := fineModel.R_refl
  rel_trans := fineModel.R_trans

/-- The valuation of Fine's model, reconstructed from [Fin74]: `φ(q₀) = {b₀}`, `φ(q₁) = {b₁}`,
`φ(r₀) = {c₀}`, `φ(r₁) = {c₁}`, `φ(p₀) = {d_{2k} : k ≥ 0}`, `φ(p₁) = {d_{2k+1} : k ≥ 0}`, and
all other atoms are valuated `∅`. Atom indices follow `Fin74.p0, .p1, .q0, .q1, .r0, .r1, .s, .t`
(`#0`–`#7`). -/
@[grind =]
protected def φ : fineModel.World → ℕ → Prop
| .b 0, 2 => True
| .b 1, 3 => True
| .c 0, 4 => True
| .c 1, 5 => True
| .d n, 0 => n % 2 = 0
| .d n, 1 => n % 2 = 1
| _, _ => False

protected def model : Model fineModel.World ℕ := ⟨fineModel.frame, fineModel.φ⟩

end fineModel


/-! ### The literal set-theoretic reconstruction of Fine's model

[Fin74, p. 25] introduces the points of the model `𝔄 = (W, R, φ)` as concrete sets, built up
by transfinite-style recursion: `b₀ = 0`, `c₀ = 1` (two distinct urelements), `b₁ = {b₀}`,
`c₁ = {c₀}`, `b_{m+2} = {b_{m+1}, c_m}`, `c_{m+2} = {b_m, c_{m+1}}`, `a_m = {b_{m+1}, c_{m+1}}`,
and `d_n = {a_m : m ≥ n}`. The accessibility relation is then defined set-theoretically as
`w fineModel.R v` iff `((∀ m) v ≠ d_m ∧ v ∈ TC({w})) ∨ ((∃ m) v = d_m ∧ w ⊇ v)`, where `TC` denotes
transitive closure.

This section transcribes that literal set-theoretic definition into Lean and proves it agrees
with the closed-form `fineModel.R`, ruling out translation errors between the two.

Two reading decisions are needed to make the transcription well-defined:

- Read literally as von Neumann ordinals, `b₀ = 0` and `c₀ = 1` would collapse the construction,
  since `b₁ = {b₀} = {0} = 1 = c₀`. To keep `b`, `c`, `a`, `d` as four genuinely distinct families,
  `b₀` and `c₀` are read as two distinct urelements (objects with no elements of their own).
- `TC({w})` is read as containing `w` itself, matching the reflexivity of `(fineModel.World,
  fineModel.R)` and the paper's own use of `fineModel.R` as a reflexive relation.

Since every element of every point of `fineModel.World` is again a point of `fineModel.World`,
"set membership" restricts to a relation `fineModel.mem : fineModel.World → fineModel.World → Prop`,
`v ∈ TC({w})` becomes `Relation.ReflTransGen fineModel.mem w v`, and `w ⊇ d_m` becomes "every element
`a_k` (`k ≥ m`) of `d_m` is an element of `w`".

- [Fin74, p. 25]
-/

namespace fineModel

/-- The literal set membership relation between points of `fineModel.World`, i.e. `fineModel.mem w v ↔ v ∈ w`,
following the set-theoretic construction of the points in [Fin74, p. 25]. -/
@[grind =]
protected def mem : fineModel.World → fineModel.World → Prop
| .b m, .b k => m = k + 1
| .b m, .c k => m = k + 2
| .c m, .c k => m = k + 1
| .c m, .b k => m = k + 2
| .a m, .b k => k = m + 1
| .a m, .c k => k = m + 1
| .d n, .a k => n ≤ k
| _, _ => False

/-- The literal set-theoretic accessibility relation from [Fin74, p. 25]: `fineModel.Rtc w v` holds iff
either `v` is not a `d`-point and `v` lies in the transitive closure of `{w}` under `fineModel.mem`, or `v`
is a `d`-point `d_m` all of whose elements are elements of `w`. -/
protected def Rtc (w v : fineModel.World) : Prop :=
  ((∀ m, v ≠ .d m) ∧ Relation.ReflTransGen fineModel.mem w v) ∨
  (∃ m, v = .d m ∧ ∀ k, m ≤ k → fineModel.mem w (.a k))

lemma mem_sub_R {x y : fineModel.World} (h : fineModel.mem x y) : fineModel.R x y := by
  cases x <;> cases y <;> simp_all [fineModel.mem, fineModel.R]

lemma reflTransGen_mem_sub_R {x y : fineModel.World} (h : Relation.ReflTransGen fineModel.mem x y) : fineModel.R x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fineModel.R_refl y
  | head h' _ ih => exact fineModel.R_trans (mem_sub_R h') ih

lemma b_descend {m k : ℕ} (h : k ≤ m) : Relation.ReflTransGen fineModel.mem (.b m) (.b k) := by
  induction m, h using Nat.le_induction with
  | base => exact .refl
  | succ n _ ih => exact .head (by simp [fineModel.mem]) ih

lemma c_descend {m k : ℕ} (h : k ≤ m) : Relation.ReflTransGen fineModel.mem (.c m) (.c k) := by
  induction m, h using Nat.le_induction with
  | base => exact .refl
  | succ n _ ih => exact .head (by simp [fineModel.mem]) ih

lemma Rtc_iff_R (w v : fineModel.World) : fineModel.Rtc w v ↔ fineModel.R w v := by
  constructor
  · rintro (⟨_, h⟩ | ⟨m, rfl, h⟩)
    · exact reflTransGen_mem_sub_R h
    · cases w with
      | b j => exact (h m le_rfl).elim
      | c j => exact (h m le_rfl).elim
      | a j => exact (h m le_rfl).elim
      | d n => exact h m le_rfl
  · intro hR
    cases w with
    | a m =>
      cases v with
      | a k => have hkm : k = m := hR; subst hkm; exact .inl ⟨fun _ => by simp, .refl⟩
      | b k => exact .inl ⟨fun _ => by simp, .head (by simp [fineModel.mem]) (b_descend hR)⟩
      | c k => exact .inl ⟨fun _ => by simp, .head (by simp [fineModel.mem]) (c_descend hR)⟩
      | d k => simp [fineModel.R] at hR
    | b m =>
      cases v with
      | a k => simp [fineModel.R] at hR
      | b k => exact .inl ⟨fun _ => by simp, b_descend hR⟩
      | c k => exact .inl ⟨fun _ => by simp, (b_descend hR).tail (by simp [fineModel.mem])⟩
      | d k => simp [fineModel.R] at hR
    | c m =>
      cases v with
      | a k => simp [fineModel.R] at hR
      | b k => exact .inl ⟨fun _ => by simp, (c_descend hR).tail (by simp [fineModel.mem])⟩
      | c k => exact .inl ⟨fun _ => by simp, c_descend hR⟩
      | d k => simp [fineModel.R] at hR
    | d n =>
      cases v with
      | a k => exact .inl ⟨fun _ => by simp, .single hR⟩
      | b k =>
        refine .inl ⟨fun _ => by simp, ?_⟩
        have h1 : fineModel.mem (.d n) (.a (max n k)) := le_max_left n k
        have h2 : fineModel.mem (.a (max n k)) (.b (max n k + 1)) := rfl
        exact ((Relation.ReflTransGen.single h1).tail h2).trans (b_descend (by omega))
      | c k =>
        refine .inl ⟨fun _ => by simp, ?_⟩
        have h1 : fineModel.mem (.d n) (.a (max n k)) := le_max_left n k
        have h2 : fineModel.mem (.a (max n k)) (.c (max n k + 1)) := rfl
        exact ((Relation.ReflTransGen.single h1).tail h2).trans (c_descend (by omega))
      | d k => exact .inr ⟨k, rfl, fun j hj => le_trans hR hj⟩

end fineModel


/-! ### Cone finiteness and confinement to the `d`-points -/

namespace fineModel

/-- The `fineModel.R`-cone of a `b`-point is finite. -/
lemma cone_b_finite (m : ℕ) : {z | fineModel.R (.b m) z}.Finite := by
  apply Set.Finite.subset (Finset.image fineModel.World.b (Finset.range (m + 1)) ∪
    Finset.image fineModel.World.c (Finset.range (m + 1))).finite_toSet;
  rintro z hz;
  cases z with
  | b k =>
    simp [fineModel.R] at hz;
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union,
      Set.mem_image, Set.mem_Iio];
    left; exact ⟨k, by omega, rfl⟩
  | c k =>
    simp [fineModel.R] at hz;
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union,
      Set.mem_image, Set.mem_Iio];
    right; exact ⟨k, by omega, rfl⟩
  | a k => simp [fineModel.R] at hz
  | d k => simp [fineModel.R] at hz

/-- The `fineModel.R`-cone of a `c`-point is finite. -/
lemma cone_c_finite (m : ℕ) : {z | fineModel.R (.c m) z}.Finite := by
  apply Set.Finite.subset (Finset.image fineModel.World.b (Finset.range (m + 1)) ∪
    Finset.image fineModel.World.c (Finset.range (m + 1))).finite_toSet;
  rintro z hz;
  cases z with
  | b k =>
    simp [fineModel.R] at hz;
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union,
      Set.mem_image, Set.mem_Iio];
    left; exact ⟨k, by omega, rfl⟩
  | c k =>
    simp [fineModel.R] at hz;
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union,
      Set.mem_image, Set.mem_Iio];
    right; exact ⟨k, by omega, rfl⟩
  | a k => simp [fineModel.R] at hz
  | d k => simp [fineModel.R] at hz

/-- The `fineModel.R`-cone of an `a`-point is finite. -/
lemma cone_a_finite (m : ℕ) : {z | fineModel.R (.a m) z}.Finite := by
  apply Set.Finite.subset ({fineModel.World.a m} ∪ Finset.image fineModel.World.b (Finset.range (m + 2)) ∪
    Finset.image fineModel.World.c (Finset.range (m + 2)) : Finset fineModel.World).finite_toSet;
  rintro z hz;
  cases z with
  | a k => simp [fineModel.R] at hz; simp [hz]
  | b k =>
    simp [fineModel.R] at hz;
    simp only [Finset.coe_union, Finset.coe_singleton, Finset.coe_image, Finset.coe_range,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_image, Set.mem_Iio];
    exact Or.inl (Or.inr ⟨k, by omega, rfl⟩)
  | c k =>
    simp [fineModel.R] at hz;
    simp only [Finset.coe_union, Finset.coe_singleton, Finset.coe_image, Finset.coe_range,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_image, Set.mem_Iio];
    exact Or.inr ⟨k, by omega, rfl⟩
  | d k => simp [fineModel.R] at hz

/-- Every infinite strict `fineModel.R`-chain in `fineModel.model` consists entirely of
`d`-points. -/
lemma strict_chain_all_d {u : ℕ → fineModel.World} (hR : ∀ m, fineModel.R (u m) (u (m + 1)))
    (hs : ∀ m, ¬fineModel.R (u (m + 1)) (u m)) (i : ℕ) : ∃ k, u i = .d k := by
  have hinj : Function.Injective u := Model.strictChain_injective (M := fineModel.model) hR hs;
  have hchain : ∀ n, fineModel.R (u i) (u (i + n)) := by
    intro n; induction n with
    | zero => simpa using fineModel.R_refl (u i)
    | succ n ih => exact fineModel.R_trans ih (hR (i + n))
  have hmem : ∀ n, u (i + n) ∈ {z | fineModel.R (u i) z} := hchain
  have hfinj : Function.Injective (fun n => u (i + n)) :=
    fun a b hab => by have := hinj hab; omega
  have hinf : {z | fineModel.R (u i) z}.Infinite := Set.infinite_of_injective_forall_mem hfinj hmem
  cases hui : u i with
  | d k => exact ⟨k, rfl⟩
  | b m => exact absurd (hui ▸ hinf) (cone_b_finite m).not_infinite
  | c m => exact absurd (hui ▸ hinf) (cone_c_finite m).not_infinite
  | a m => exact absurd (hui ▸ hinf) (cone_a_finite m).not_infinite

end fineModel

end Fin74

end
