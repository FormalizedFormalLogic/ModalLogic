module

public import Neighborhood.Formula.Basic

/-!
# Axiom schemes

Axiom schemes of classical propositional logic and of modal logic, as reducible
abbreviations for the corresponding formulas.
-/

@[expose] public section

namespace Axioms

variable {α : Type u} (A B C : Formula α)

protected abbrev ImplyK := A 🡒 B 🡒 A

protected abbrev ImplyS := (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 A 🡒 C

protected abbrev ElimContra := (∼B 🡒 ∼A) 🡒 (A 🡒 B)

protected abbrev DNE := ∼∼A 🡒 A

protected abbrev AndElim₁ := A ⋏ B 🡒 A

protected abbrev AndElim₂ := A ⋏ B 🡒 B

protected abbrev AndIntro := A 🡒 B 🡒 A ⋏ B

protected abbrev OrIntro₁ := A 🡒 A ⋎ B

protected abbrev OrIntro₂ := B 🡒 A ⋎ B

protected abbrev OrElim := (A 🡒 C) 🡒 (B 🡒 C) 🡒 (A ⋎ B 🡒 C)

protected abbrev K := □(A 🡒 B) 🡒 □A 🡒 □B

protected abbrev M := □(A ⋏ B) 🡒 (□A ⋏ □B)

protected abbrev C := (□A ⋏ □B) 🡒 □(A ⋏ B)

protected abbrev N : Formula α := □(⊤ : Formula α)

/-- Axiom for reflexivity. -/
protected abbrev T := □A 🡒 A

/-- Axiom for symmetry. -/
protected abbrev B := A 🡒 □◇A

/-- Axiom for seriality. -/
protected abbrev D := □A 🡒 ◇A

/-- Alternative axiom `D`. -/
protected abbrev P : Formula α := ∼(□⊥)

/-- Axiom for transitivity. -/
protected abbrev Four := □A 🡒 □□A

/-- Axiom for euclideanness. -/
protected abbrev Five := ◇A 🡒 □◇A

/-- Parameters `i`, `j`, `m`, `n` of the Geach axiom scheme. -/
protected structure Geach.Taple where
  i : ℕ
  j : ℕ
  m : ℕ
  n : ℕ

/-- Axiom for Geach convergence. -/
protected abbrev Geach (g : Geach.Taple) (A : Formula α) := (◇^[g.i](□^[g.m]A)) 🡒 (□^[g.j](◇^[g.n]A))

end Axioms

end
