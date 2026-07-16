module

public import Fin74.Logic.Basic
public import Fin74.Kripke.Basic

@[expose]
public section

namespace Fin74

/-- The substitution `σ_m` of [Fin74]: `q₀ ↦ B m`, `q₁ ↦ B (m+1)`, `r₀ ↦ C m`, `r₁ ↦ C (m+1)`,
identity elsewhere. -/
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

/-- Auxiliary result (1) of [Fin74]: shifting `B`/`C` by `σ_m` advances their index by `m`.
Proved by joint recursion on `n`, mirroring the mutual recursion of `B`/`C`. -/
theorem B_C_subst_shift (m n : ℕ) : (B n)⟦shift m⟧ = B (m + n) ∧ (C n)⟦shift m⟧ = C (m + n) :=
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

theorem B_subst_shift (m n : ℕ) : (B n)⟦shift m⟧ = B (m + n) := (B_C_subst_shift m n).1
theorem C_subst_shift (m n : ℕ) : (C n)⟦shift m⟧ = C (m + n) := (B_C_subst_shift m n).2

@[simp, grind =]
theorem A_subst_shift (m n : ℕ) : (A n)⟦shift m⟧ = A (m + n) := by
  simp [A, B_subst_shift, C_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
theorem D_subst_shift (m : ℕ) : D⟦shift m⟧ = D := by
  simp [D]

/-- `K^m` of [Fin74]: the four conjuncts asserting how `B_{m+1}`/`C_{m+1}` relate to their
neighbours. Split into four pieces (`K1`–`K4`) so each can be established independently. -/
def K1 (m : ℕ) : Formula ℕ := □(B (m + 1) 🡒 (◇(B m) ⋏ ∼◇(C m)))
def K2 (m : ℕ) : Formula ℕ := □(C (m + 1) 🡒 (◇(C m) ⋏ ∼◇(B m)))
def K3 (m : ℕ) : Formula ℕ := □(B m 🡒 ∼◇(B (m + 1)))
def K4 (m : ℕ) : Formula ℕ := □(C m 🡒 ∼◇(C (m + 1)))

/-- `K^m` of [Fin74]: the conjunction of the last four conjuncts of `E^m`. -/
def K (m : ℕ) : Formula ℕ := K1 m ⋏ K2 m ⋏ K3 m ⋏ K4 m

@[simp, grind =]
theorem K1_subst_shift (m n : ℕ) : (K1 n)⟦shift m⟧ = K1 (m + n) := by
  simp [K1, B_subst_shift, C_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
theorem K2_subst_shift (m n : ℕ) : (K2 n)⟦shift m⟧ = K2 (m + n) := by
  simp [K2, B_subst_shift, C_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
theorem K3_subst_shift (m n : ℕ) : (K3 n)⟦shift m⟧ = K3 (m + n) := by
  simp [K3, B_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
theorem K4_subst_shift (m n : ℕ) : (K4 n)⟦shift m⟧ = K4 (m + n) := by
  simp [K4, C_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
theorem K_subst_shift (m n : ℕ) : (K n)⟦shift m⟧ = K (m + n) := by
  simp [K, K1_subst_shift, K2_subst_shift, K3_subst_shift, K4_subst_shift]

variable {κ : Type*} {M : Model κ ℕ} {x : M.World} {m : ℕ}

/-- Forcing characterization of `E` at level `0`. -/
theorem forces_E_iff : x ⊩ E ↔ x ⊩ D ∧ x ⊩ ◇(A 0) ∧ x ⊩ K 0 := by
  simp [E, K, K1, K2, K3, K4, Model.World.forces_and];
  tauto

/-- Forcing characterization of `E⟦σ_m⟧`: the shifted `E` is (up to forcing) `D` together
with `◇(A m)` and the shifted `K`-block. Do not `simp`/`grind`-unfold `E` directly beyond
this point — cite this lemma instead. -/
theorem forces_E_subst_shift : x ⊩ E⟦shift m⟧ ↔ x ⊩ D ∧ x ⊩ ◇(A m) ∧ x ⊩ K m := by
  simp [E, K, K1, K2, K3, K4, D_subst_shift, A_subst_shift, Model.World.forces_and];
  tauto

/-- Forcing characterization of `F⟦σ_m⟧`. -/
theorem forces_F_subst_shift :
    x ⊩ F⟦shift m⟧ ↔ ∃ y, x ≺ y ∧ y ⊩ p0 ⋎ p1 ∧ y ⊩ ∼◇(A m) ∧ y ⊩ ◇(A (m + 1)) := by
  simp [F, A_subst_shift, Model.World.forces_dia, Model.World.forces_and];
  tauto

end Fin74

end
