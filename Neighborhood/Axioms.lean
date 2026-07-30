module

public import Neighborhood.Formula.Basic

/-!
# Axiom schemes

Axiom schemes of classical propositional logic and of modal logic, as reducible
abbreviations for the corresponding formulas.
-/

@[expose] public section

namespace LO.Modal.Axioms

variable (φ ψ χ : Formula)

protected abbrev ImplyK := φ 🡒 ψ 🡒 φ

protected abbrev ImplyS := (φ 🡒 ψ 🡒 χ) 🡒 (φ 🡒 ψ) 🡒 φ 🡒 χ

protected abbrev ElimContra := (∼ψ 🡒 ∼φ) 🡒 (φ 🡒 ψ)

protected abbrev K := □(φ 🡒 ψ) 🡒 □φ 🡒 □ψ

protected abbrev M := □(φ ⋏ ψ) 🡒 (□φ ⋏ □ψ)

protected abbrev C := (□φ ⋏ □ψ) 🡒 □(φ ⋏ ψ)

protected abbrev N : Formula := □(⊤ : Formula)

/-- Axiom for reflexivity. -/
protected abbrev T := □φ 🡒 φ

/-- Axiom for symmetry. -/
protected abbrev B := φ 🡒 □◇φ

/-- Axiom for seriality. -/
protected abbrev D := □φ 🡒 ◇φ

/-- Alternative axiom `D`. -/
protected abbrev P : Formula := ∼(□⊥)

/-- Axiom for transitivity. -/
protected abbrev Four := □φ 🡒 □□φ

/-- Axiom for euclideanness. -/
protected abbrev Five := ◇φ 🡒 □◇φ

/-- Parameters `i`, `j`, `m`, `n` of the Geach axiom scheme. -/
protected structure Geach.Taple where
  i : ℕ
  j : ℕ
  m : ℕ
  n : ℕ

/-- Axiom for Geach convergence. -/
protected abbrev Geach (g : Geach.Taple) (φ : Formula) := (◇^[g.i](□^[g.m]φ)) 🡒 (□^[g.j](◇^[g.n]φ))

end LO.Modal.Axioms

end
