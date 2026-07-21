module

public import Fin74.Kripke.Basic

@[expose]
public section

abbrev Logic {α} := Set (Formula α)

instance {α} : Membership (Formula α) (@Logic α) := inferInstanceAs (Membership (Formula α) (Set (Formula α)))

/-- The logic generated over `X` by classical propositional logic (axiomatized à la
Łukasiewicz by `implyK`/`implyS`/`elimContra`, as in `Foundation`'s
`Entailment.Łukasiewicz`), the modal axioms `K`/`T`/`4`, the extra axioms in `X`, and
closure under modus ponens, necessitation, and uniform substitution. -/
inductive mkLogic (X : @Logic α) : Formula α → Prop
| implyK {A B} : mkLogic X $ A 🡒 B 🡒 A
| implyS {A B C} : mkLogic X $ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)
| elimContra {A B} : mkLogic X $ (∼B 🡒 ∼A) 🡒 (A 🡒 B)
| axiomK {A B} : mkLogic X $ (□(A 🡒 B)) 🡒 (□A 🡒 □B)
| axiomT {A} : mkLogic X $ □A 🡒 A
| axiom4 {A} : mkLogic X $ □A 🡒 □□A
| addAxiom {A} : A ∈ X → mkLogic X A
| mp {A B} : mkLogic X (A 🡒 B) → mkLogic X A → mkLogic X B
| nec {A} : mkLogic X A → mkLogic X (□A)
| subst {A} {σ} : mkLogic X A → mkLogic X (A⟦σ⟧)

abbrev LogicS4 : @Logic α := mkLogic ∅


namespace Fin74

def p0 : Formula ℕ := #0
def p1 : Formula ℕ := #1
def q0 : Formula ℕ := #2
def q1 : Formula ℕ := #3
def r0 : Formula ℕ := #4
def r1 : Formula ℕ := #5
def s  : Formula ℕ := #6
def t  : Formula ℕ := #7

mutual

/-- `B_m`.

- [Fin74] -/
def B : ℕ → Formula ℕ
| 0     => q0
| 1     => q1
| m + 2 => ◇(B (m + 1)) ⋏ ◇(C m) ⋏ ∼◇(C (m + 1))

/-- `C_m`, a mirror image of `B`; the recursive clause here corrects a typo in the original
(which has `∼◇(B (m + 2))` instead).

- [Fin74]
- [Lit04, p. 332] -/
def C : ℕ → Formula ℕ
| 0     => r0
| 1     => r1
| m + 2 => ◇(C (m + 1)) ⋏ ◇(B m) ⋏ ∼◇(B (m + 1))

end

@[simp, grind =] lemma B_zero : B 0 = q0 := by simp [B]
@[simp, grind =] lemma B_one : B 1 = q1 := by simp [B]
@[simp, grind =] lemma B_add_two (m : ℕ) : B (m + 2) = ◇(B (m + 1)) ⋏ ◇(C m) ⋏ ∼◇(C (m + 1)) := by simp [B]

@[simp, grind =] lemma C_zero : C 0 = r0 := by simp [C]
@[simp, grind =] lemma C_one : C 1 = r1 := by simp [C]
@[simp, grind =] lemma C_add_two (m : ℕ) : C (m + 2) = ◇(C (m + 1)) ⋏ ◇(B m) ⋏ ∼◇(B (m + 1)) := by simp [C]

/-- `A_m`, with a fourth conjunct `∼◇(C (m + 2))` mirroring the third; the original has only
three conjuncts.

- [Fin74]
- [Lit04, p. 332] -/
def A (m : ℕ) : Formula ℕ := ◇(B (m + 1)) ⋏ ◇(C (m + 1)) ⋏ ∼◇(B (m + 2)) ⋏ ∼◇(C (m + 2))

/-- `D`, with the guard on `p₁` stated in both directions; the original states only one
direction.

- [Fin74]
- [Lit04, p. 332] -/
def D : Formula ℕ :=
  (p0 ⋎ p1) ⋏ □(p0 🡒 (∼p1 ⋏ ◇p1)) ⋏ □(p1 🡒 (∼p0 ⋏ ◇p0)) ⋏ □(∼(p0 ⋎ p1) 🡒 □(∼(p0 ⋎ p1)))

/-- `κ`'s first conjunct at level `m`. -/
def K1 (m : ℕ) : Formula ℕ := □(B (m + 1) 🡒 (◇(B m) ⋏ ∼◇(C m)))

/-- `κ`'s second conjunct at level `m`. -/
def K2 (m : ℕ) : Formula ℕ := □(C (m + 1) 🡒 (◇(C m) ⋏ ∼◇(B m)))

/-- `κ`'s third conjunct at level `m`. -/
def K3 (m : ℕ) : Formula ℕ := □(B m 🡒 ∼◇(B (m + 1)))

/-- `κ`'s fourth conjunct at level `m`. -/
def K4 (m : ℕ) : Formula ℕ := □(C m 🡒 ∼◇(C (m + 1)))

/-- `K^m`: the conjunction of `K1`–`K4` at level `m`, indexed by `ℕ` rather than inlined at
level `0` as in the original.

- [Fin74] -/
def K (m : ℕ) : Formula ℕ := K1 m ⋏ K2 m ⋏ K3 m ⋏ K4 m

/-- `E`.

- [Fin74] -/
def E : Formula ℕ := D ⋏ ◇(A 0) ⋏ K 0

/-- `F`.

- [Fin74] -/
def F : Formula ℕ := ◇((p0 ⋎ p1) ⋏ ∼◇(A 0) ⋏ ◇(A 1))

/-- `G`.

- [Fin74] -/
def G : Formula ℕ := E 🡒 F

/-- `H`.

- [Fin74] -/
def H : Formula ℕ := ∼(s ⋏ □(s 🡒 ◇(∼s ⋏ t ⋏ ◇((∼s ⋏ ∼t) ⋏ ◇s))))

/-- The logic `L`: `S4` extended by the axioms `G` and `H`.

- [Fin74]
- [Ger75, §4]
- [Lit04, p. 332] -/
abbrev LogicFi : @Logic ℕ := mkLogic {G, H}

end Fin74


/-! ### The `K`-block climbs one level along the accessibility relation -/

namespace Fin74

variable {κ : Type*} {M : Model κ ℕ} {x y : M.World} {m n : ℕ}

open Model.World

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_K1_succ : x ⊩ K1 (m + 1) := by grind [K1];

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_K2_succ : x ⊩ K2 (m + 1) := by grind [K2];

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_K3_succ_of_K1 (h1 : x ⊩ K1 m) (Rxy : x ≺ y) : y ⊩ K3 (m + 1) := by grind [K1, K3];

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_K4_succ_of_K2 (h2 : x ⊩ K2 m) (Rxy : x ≺ y) : y ⊩ K4 (m + 1) := by grind [K2, K4];

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_K_succ (hK : x ⊩ K m) (Rxy : x ≺ y) : y ⊩ K (m + 1) := by
  grind [K, forces_K1_succ, forces_K2_succ, forces_K3_succ_of_K1, forces_K4_succ_of_K2];

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_K_succ' (hK : x ⊩ K m) : x ⊩ K (m + 1) := forces_K_succ hK (M.rel_refl x)

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
theorem forces_K_mono (hnm : n ≤ m) (hK : x ⊩ K n) : x ⊩ K m := by
  induction m, hnm using Nat.le_induction with
  | base => exact hK
  | succ m _ ih => exact forces_K_succ' ih

end Fin74


/-! ### The shift substitution `σ_m` -/

namespace Fin74

/-- The substitution `σ_m`: `q₀ ↦ B m`, `q₁ ↦ B (m+1)`, `r₀ ↦ C m`, `r₁ ↦ C (m+1)`, identity
elsewhere.

- [Fin74] -/
def shift (m : ℕ) : Formula.Substitution ℕ ℕ
| 2 => B m
| 3 => B (m + 1)
| 4 => C m
| 5 => C (m + 1)
| a => #a

@[simp, grind =] lemma shift_p0 (m : ℕ) : p0⟦shift m⟧ = p0 := rfl
@[simp, grind =] lemma shift_p1 (m : ℕ) : p1⟦shift m⟧ = p1 := rfl
@[simp, grind =] lemma shift_q0 (m : ℕ) : q0⟦shift m⟧ = B m := rfl
@[simp, grind =] lemma shift_q1 (m : ℕ) : q1⟦shift m⟧ = B (m + 1) := rfl
@[simp, grind =] lemma shift_r0 (m : ℕ) : r0⟦shift m⟧ = C m := rfl
@[simp, grind =] lemma shift_r1 (m : ℕ) : r1⟦shift m⟧ = C (m + 1) := rfl
@[simp, grind =] lemma shift_s (m : ℕ) : s⟦shift m⟧ = s := rfl
@[simp, grind =] lemma shift_t (m : ℕ) : t⟦shift m⟧ = t := rfl

lemma B_C_subst_shift (m n : ℕ) : (B n)⟦shift m⟧ = B (m + n) ∧ (C n)⟦shift m⟧ = C (m + n) :=
  -- Joint recursion on `n`, mirroring the mutual recursion of `B`/`C`.
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    obtain ⟨ihB1, ihC1⟩ := B_C_subst_shift m (n + 1);
    obtain ⟨ihB0, ihC0⟩ := B_C_subst_shift m n;
    have : m + (n + 1) = m + n + 1 := by omega;
    have : m + (n + 2) = m + n + 2 := by omega;
    constructor;
    . simp_all;
    . simp_all;

lemma B_subst_shift (m n : ℕ) : (B n)⟦shift m⟧ = B (m + n) := (B_C_subst_shift m n).1
lemma C_subst_shift (m n : ℕ) : (C n)⟦shift m⟧ = C (m + n) := (B_C_subst_shift m n).2

@[simp, grind =]
lemma A_subst_shift (m n : ℕ) : (A n)⟦shift m⟧ = A (m + n) := by
  simp [A, B_subst_shift, C_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma D_subst_shift (m : ℕ) : D⟦shift m⟧ = D := by
  simp [D]

@[simp, grind =]
lemma K1_subst_shift (m n : ℕ) : (K1 n)⟦shift m⟧ = K1 (m + n) := by
  simp [K1, B_subst_shift, C_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma K2_subst_shift (m n : ℕ) : (K2 n)⟦shift m⟧ = K2 (m + n) := by
  simp [K2, B_subst_shift, C_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma K3_subst_shift (m n : ℕ) : (K3 n)⟦shift m⟧ = K3 (m + n) := by
  simp [K3, B_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma K4_subst_shift (m n : ℕ) : (K4 n)⟦shift m⟧ = K4 (m + n) := by
  simp [K4, C_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma K_subst_shift (m n : ℕ) : (K n)⟦shift m⟧ = K (m + n) := by
  simp [K, K1_subst_shift, K2_subst_shift, K3_subst_shift, K4_subst_shift]

variable {κ : Type*} {M : Model κ ℕ} {x : M.World} {m : ℕ}

lemma forces_E_iff : x ⊩ E ↔ x ⊩ D ∧ x ⊩ ◇(A 0) ∧ x ⊩ K 0 := by
  simp [E, K, K1, K2, K3, K4, Model.World.forces_and];
  tauto

/-- Do not `simp`/`grind`-unfold `E` directly beyond this point — cite this lemma instead. -/
lemma forces_E_subst_shift : x ⊩ E⟦shift m⟧ ↔ x ⊩ D ∧ x ⊩ ◇(A m) ∧ x ⊩ K m := by
  simp [E, K, K1, K2, K3, K4, D_subst_shift, A_subst_shift, Model.World.forces_and];
  tauto

lemma forces_F_subst_shift : x ⊩ F⟦shift m⟧ ↔ ∃ y, x ≺ y ∧ y ⊩ p0 ⋎ p1 ∧ y ⊩ ∼◇(A m) ∧ y ⊩ ◇(A (m + 1)) := by
  simp [F, A_subst_shift, Model.World.forces_dia, Model.World.forces_and];
  tauto

end Fin74

end
