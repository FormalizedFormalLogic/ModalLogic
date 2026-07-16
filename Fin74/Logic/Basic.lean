module

public import Foundation.Vorspiel.Set.Basic
public import Fin74.Formula.Substitution

@[expose]
public section

abbrev Logic {α} := Set (Formula α)

/-- The logic generated over `X` by classical propositional logic (axiomatized à la
Łukasiewicz by `implyK`/`implyS`/`elimContra`, as in `Foundation`'s
`Entailment.Łukasiewicz`), the modal axioms `K`/`T`/`4`, the extra axioms in `X`, and
closure under modus ponens, necessitation, and uniform substitution. -/
inductive mkLogic (X : Set (Formula α)) : Formula α → Prop
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

/-- The eight propositional atoms `p₀, p₁, q₀, q₁, r₀, r₁, s, t` used to build the formula
family below, fixed as distinct natural numbers. -/
def p0 : Formula ℕ := #0
def p1 : Formula ℕ := #1
def q0 : Formula ℕ := #2
def q1 : Formula ℕ := #3
def r0 : Formula ℕ := #4
def r1 : Formula ℕ := #5
def s  : Formula ℕ := #6
def t  : Formula ℕ := #7

mutual

/-- `B_m` from [Fin74], defined by mutual recursion with `C`: `C_{m+2}` refers to the
just-computed `B_{m+2}`, so the two families cannot be defined independently. -/
def B : ℕ → Formula ℕ
| 0     => q0
| 1     => q1
| m + 2 => ◇(B (m + 1)) ⋏ ◇(C m) ⋏ ∼◇(C (m + 1))

/-- `C_m` from [Fin74]; see `B`. -/
def C : ℕ → Formula ℕ
| 0     => r0
| 1     => r1
| m + 2 => ◇(C (m + 1)) ⋏ ◇(B m) ⋏ ∼◇(B (m + 2))

end

@[simp, grind =] lemma B_zero : B 0 = q0 := by simp [B]
@[simp, grind =] lemma C_zero : C 0 = r0 := by simp [C]
@[simp, grind =] lemma B_one : B 1 = q1 := by simp [B]
@[simp, grind =] lemma C_one : C 1 = r1 := by simp [C]

@[simp, grind =]
lemma B_add_two (m : ℕ) : B (m + 2) = ◇(B (m + 1)) ⋏ ◇(C m) ⋏ ∼◇(C (m + 1)) := by simp [B]

@[simp, grind =]
lemma C_add_two (m : ℕ) : C (m + 2) = ◇(C (m + 1)) ⋏ ◇(B m) ⋏ ∼◇(B (m + 2)) := by simp [C]

/-- `A_m` from [Fin74]. -/
def A (m : ℕ) : Formula ℕ := ◇(B (m + 1)) ⋏ ◇(C (m + 1)) ⋏ ∼◇(B (m + 2))

/-- `D` from [Fin74]. -/
def D : Formula ℕ :=
  (p0 ⋎ p1) ⋏ □(p0 🡒 (∼p1 ⋏ ◇p1)) ⋏ □(∼(p0 ⋎ p1) 🡒 □(∼(p0 ⋎ p1)))

/-- `E` from [Fin74]. -/
def E : Formula ℕ :=
  D ⋏ ◇(A 0)
    ⋏ □(B 1 🡒 ◇(B 0) ⋏ ∼◇(C 0))
    ⋏ □(C 1 🡒 ◇(C 0) ⋏ ∼◇(B 0))
    ⋏ □(B 0 🡒 ∼◇(B 1))
    ⋏ □(C 0 🡒 ∼◇(C 1))

/-- `F` from [Fin74]. -/
def F : Formula ℕ := ◇((p0 ⋎ p1) ⋏ ∼◇(A 0) ⋏ ◇(A 1))

/-- `G` from [Fin74]. -/
def G : Formula ℕ := E 🡒 F

/-- `H` from [Fin74]. -/
def H : Formula ℕ :=
  ∼(s ⋏ □(s 🡒 ◇(∼s ⋏ t ⋏ ◇((∼s ⋏ ∼t) ⋏ ◇s))))

/-- The logic `L` of [Fin74]: `S4` extended by the axioms `G` and `H`. -/
abbrev LogicFi : @Logic ℕ := mkLogic {G, H}

end Fin74

end
