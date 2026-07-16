module

public import Fin74.Formula.Substitution

@[expose]
public section

/-- A Kripke model whose accessibility relation is reflexive and transitive (the paper
[Fin74] only ever considers such models, so this is baked into the structure rather than
imposed via a separate typeclass). -/
structure Model (κ : Type u) (α : Type v) where
  Rel'      : κ → κ → Prop
  rel_refl  : ∀ x, Rel' x x
  rel_trans : ∀ {x y z}, Rel' x y → Rel' y z → Rel' x z
  Val'      : κ → α → Prop

instance : CoeFun (Model κ α) (fun _ => κ → α → Prop) := ⟨Model.Val'⟩

namespace Model

variable {M : Model κ α}

abbrev World (_ : Model κ α) := κ

abbrev Val {M : Model κ α} : M.World → α → Prop := M.Val'

abbrev Rel {M : Model κ α} : M.World → M.World → Prop := M.Rel'
infixl:60 " ≺ " => Rel

@[grind .] lemma rel_refl' (x : M.World) : x ≺ x := M.rel_refl x
@[grind →] lemma rel_trans' {x y z : M.World} (hxy : x ≺ y) (hyz : y ≺ z) : x ≺ z := M.rel_trans hxy hyz

end Model


namespace Model.World

variable {M : Model κ α} {x : M.World} {A B : Formula α}

@[grind =]
def Forces (x : M.World) : Formula α → Prop
| #a    => M x a
| ⊥     => False
| A 🡒 B => Forces x A → Forces x B
| ◇A    => ∃ y, x ≺ y ∧ Forces y A
infix:55 " ⊩ " => Forces

abbrev NotForces (x : M.World) (A : Formula α) : Prop := ¬x ⊩ A
infix:55 " ⊮ " => NotForces

@[simp, grind .] lemma forces_top : x ⊩ ⊤ := by grind;
@[grind =] lemma forces_imp : x ⊩ A 🡒 B ↔ x ⊮ A ∨ x ⊩ B := by grind;
@[grind =] lemma forces_and : x ⊩ A ⋏ B ↔ x ⊩ A ∧ x ⊩ B := by grind;
@[grind =] lemma forces_or  : x ⊩ A ⋎ B ↔ x ⊩ A ∨ x ⊩ B := by grind;
@[grind =] lemma forces_iff : x ⊩ A 🡘 B ↔ (x ⊩ A ↔ x ⊩ B) := by grind;
@[grind =] lemma forces_neg : x ⊩ ∼A ↔ x ⊮ A := by grind;
@[grind =] lemma forces_dia : x ⊩ ◇A ↔ ∃ y, x ≺ y ∧ y ⊩ A := by grind;
@[grind =] lemma forces_box : x ⊩ □A ↔ ∀ y, x ≺ y → y ⊩ A := by grind;

@[simp, grind .] lemma not_forces_bot : x ⊮ ⊥ := by grind;
@[grind =] lemma not_forces_and : x ⊮ A ⋏ B ↔ x ⊮ A ∨ x ⊮ B := by grind;
@[grind =] lemma not_forces_or  : x ⊮ A ⋎ B ↔ x ⊮ A ∧ x ⊮ B := by grind;
@[grind =] lemma not_forces_neg : x ⊮ ∼A ↔ x ⊩ A := by grind;
@[grind =] lemma not_forces_imp : x ⊮ A 🡒 B ↔ x ⊩ A ∧ x ⊮ B := by grind;
@[grind =] lemma not_forces_dia : x ⊮ ◇A ↔ ∀ y, x ≺ y → y ⊮ A := by grind;
@[grind =] lemma not_forces_box : x ⊮ □A ↔ ∃ y, x ≺ y ∧ y ⊮ A := by grind;

end Model.World


namespace Model

variable {M : Model κ α} {A : Formula α}

/-- `M` satisfies `A` at every world, i.e. `A` is valid on `M`. -/
@[grind =]
def Validate (M : Model κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
infix:50 " ⊧ " => Model.Validate

/-- `M` strongly verifies `A`: every uniform substitution instance of `A` is valid on `M`.
(This is the notion of "strongly verified" from [Fin74]: `A` remains valid on `M` no matter
which formulas are substituted for its atoms.) -/
@[grind =]
def StronglyVerifies (M : Model κ α) (A : Formula α) : Prop := ∀ σ, M ⊧ (A⟦σ⟧)

end Model

end
