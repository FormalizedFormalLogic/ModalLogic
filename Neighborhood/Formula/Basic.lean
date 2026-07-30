module

public import Mathlib.Data.Finset.Basic

/-!
# Modal formulas

Formulas of propositional modal logic over a type `α` of propositional variables.

The primitive connectives are `atom`, `⊥`, `🡒` and `□`; negation, verum, conjunction,
disjunction, biimplication and `◇` are reducible abbreviations of those, so that e.g.
`◇A = ∼□∼A` and `∼A = A 🡒 ⊥` hold by `rfl`.
-/

@[expose] public section

/-- Formulas of propositional modal logic. -/
inductive Formula (α : Type u) where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq

abbrev FormulaSet (α : Type u) := Set (Formula α)

abbrev FormulaFinset (α : Type u) := Finset (Formula α)

namespace Formula

variable {α : Type u} {n : ℕ} {A A₁ A₂ B B₁ B₂ : Formula α}

instance : Bot (Formula α) := ⟨falsum⟩

@[match_pattern] abbrev neg (A : Formula α) : Formula α := imp A ⊥

@[match_pattern] abbrev verum : Formula α := neg ⊥

instance : Top (Formula α) := ⟨verum⟩

@[match_pattern] abbrev or (A B : Formula α) : Formula α := imp (neg A) B

@[match_pattern] abbrev and (A B : Formula α) : Formula α := neg (imp A (neg B))

@[match_pattern] abbrev dia (A : Formula α) : Formula α := neg (box (neg A))

@[match_pattern] abbrev iff (A B : Formula α) : Formula α := and (imp A B) (imp B A)

end Formula

@[inherit_doc] prefix:75 "∼" => Formula.neg
@[inherit_doc] infixr:60 " 🡒 " => Formula.imp
@[inherit_doc] infixr:69 " ⋏ " => Formula.and
@[inherit_doc] infixr:68 " ⋎ " => Formula.or
@[inherit_doc] infix:61 " 🡘 " => Formula.iff
@[inherit_doc] prefix:76 "□" => Formula.box
@[inherit_doc] prefix:76 "◇" => Formula.dia

namespace Formula

variable {α : Type u} {n : ℕ} {A A₁ A₂ B B₁ B₂ : Formula α}

@[grind =] lemma eq_verum_neg_falsum : ⊤ = ∼(⊥ : Formula α) := rfl

lemma falsum_eq : (⊥ : Formula α) = falsum := rfl
lemma verum_eq : (⊤ : Formula α) = verum := rfl
lemma iff_eq : A 🡘 B = (A 🡒 B) ⋏ (B 🡒 A) := rfl
attribute [grind =_] falsum_eq verum_eq iff_eq

@[grind =] lemma inj_and : A₁ ⋏ A₂ = B₁ ⋏ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := by simp [and]
@[grind =] lemma inj_or : A₁ ⋎ A₂ = B₁ ⋎ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := by simp [or]
@[grind =] lemma inj_imp : A₁ 🡒 A₂ = B₁ 🡒 B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := by simp
@[grind =] lemma inj_neg : ∼A = ∼B ↔ A = B := by simp [neg]
@[grind =] lemma inj_box : □A = □B ↔ A = B := by simp
@[grind =] lemma inj_dia : ◇A = ◇B ↔ A = B := by simp [dia]

/-- Formula complexity. -/
@[grind =]
def complexity : Formula α → ℕ
  | atom _ => 0
  | ⊥      => 0
  | A 🡒 B  => max A.complexity B.complexity + 1
  | □A     => A.complexity + 1

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a, C (atom a))
    (himp : ∀ A B, C (A 🡒 B))
    (hbox : ∀ A, C (□A))
    : (A : Formula α) → C A
  | ⊥      => hfalsum
  | atom a => hatom a
  | □A     => hbox A
  | A 🡒 B  => himp A B

@[induction_eliminator]
def rec' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a, C (atom a))
    (himp : ∀ A B, C A → C B → C (A 🡒 B))
    (hbox : ∀ A, C A → C (□A))
    : (A : Formula α) → C A
  | ⊥      => hfalsum
  | atom a => hatom a
  | A 🡒 B  => himp A B (rec' hfalsum hatom himp hbox A) (rec' hfalsum hatom himp hbox B)
  | □A     => hbox A (rec' hfalsum hatom himp hbox A)

/-- Iterated `□`. -/
abbrev multibox (n : ℕ) : Formula α → Formula α := (□·)^[n]

@[inherit_doc] notation:76 "□^[" n "]" A:80 => Formula.multibox n A

/-- Iterated `◇`. -/
abbrev multidia (n : ℕ) : Formula α → Formula α := (◇·)^[n]

@[inherit_doc] notation:76 "◇^[" n "]" A:80 => Formula.multidia n A

@[simp, grind =] lemma multibox_zero : (□^[0]A) = A := rfl
@[simp, grind =] lemma multibox_succ : (□^[n + 1]A) = □(□^[n]A) := Function.iterate_succ_apply' ..
@[simp, grind =] lemma multibox_add {m : ℕ} : (□^[n](□^[m]A)) = □^[n + m]A :=
  (Function.iterate_add_apply _ n m A).symm

@[simp, grind =] lemma multidia_zero : (◇^[0]A) = A := rfl
@[simp, grind =] lemma multidia_succ : (◇^[n + 1]A) = ◇(◇^[n]A) := Function.iterate_succ_apply' ..
@[simp, grind =] lemma multidia_add {m : ℕ} : (◇^[n](◇^[m]A)) = ◇^[n + m]A :=
  (Function.iterate_add_apply _ n m A).symm

end Formula

/-- A substitution of formulas for propositional variables. -/
abbrev Substitution (α : Type u) := α → Formula α

/-- Simultaneous substitution of formulas for propositional variables. -/
def Formula.subst (s : Substitution α) : Formula α → Formula α
  | atom a => s a
  | ⊥      => ⊥
  | □A     => □(A.subst s)
  | A 🡒 B  => A.subst s 🡒 B.subst s

@[inherit_doc] notation:80 A "⟦" s "⟧" => Formula.subst s A

namespace Formula.subst

variable {α : Type u} {n : ℕ} {s : Substitution α} {A B : Formula α}

lemma subst_atom {a} : (atom a)⟦s⟧ = s a := rfl
lemma subst_falsum : (⊥ : Formula α)⟦s⟧ = ⊥ := rfl
lemma subst_verum : (⊤ : Formula α)⟦s⟧ = ⊤ := rfl
lemma subst_imp : (A 🡒 B)⟦s⟧ = A⟦s⟧ 🡒 B⟦s⟧ := rfl
lemma subst_neg : (∼A)⟦s⟧ = ∼(A⟦s⟧) := rfl
lemma subst_and : (A ⋏ B)⟦s⟧ = A⟦s⟧ ⋏ B⟦s⟧ := rfl
lemma subst_or : (A ⋎ B)⟦s⟧ = A⟦s⟧ ⋎ B⟦s⟧ := rfl
lemma subst_iff : (A 🡘 B)⟦s⟧ = (A⟦s⟧ 🡘 B⟦s⟧) := rfl
attribute [simp, grind =]
  subst_atom
  subst_falsum
  subst_verum
  subst_neg
  subst_and
  subst_or
  subst_imp
  subst_iff

@[simp, grind =] lemma subst_box : (□A)⟦s⟧ = □(A⟦s⟧) := rfl
@[simp, grind =] lemma subst_multibox : (□^[n]A)⟦s⟧ = □^[n](A⟦s⟧) := by induction n <;> simp_all;
@[simp, grind =] lemma subst_dia : (◇A)⟦s⟧ = ◇(A⟦s⟧) := rfl
@[simp, grind =] lemma subst_multidia : (◇^[n]A)⟦s⟧ = ◇^[n](A⟦s⟧) := by induction n <;> simp_all;

end Formula.subst

/-- The identity substitution. -/
abbrev Substitution.id {α : Type u} : Substitution α := .atom

@[simp] lemma Formula.subst.def_id {α : Type u} {A : Formula α} : A⟦.id⟧ = A := by
  induction A <;> simp_all;

/-- Composition of substitutions. -/
def Substitution.comp {α : Type u} (s₁ s₂ : Substitution α) : Substitution α := fun a => (s₁ a)⟦s₂⟧

@[simp]
lemma Formula.subst.def_comp {α : Type u} {s₁ s₂ : Substitution α} {A : Formula α} :
    A⟦s₁.comp s₂⟧ = A⟦s₁⟧⟦s₂⟧ := by
  induction A <;> simp_all [Substitution.comp];

end
