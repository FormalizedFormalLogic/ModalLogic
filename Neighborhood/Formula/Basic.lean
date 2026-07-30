module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Notation

/-!
# Modal formulas

Formulas of propositional modal logic over the natural numbers as propositional variables.

The primitive connectives are `atom`, `⊥`, `🡒` and `□`; negation, verum, conjunction,
disjunction, biimplication and `◇` are reducible abbreviations of those, so that e.g.
`◇φ = ∼□∼φ` and `∼φ = φ 🡒 ⊥` hold by `rfl`.
-/

@[expose] public section

namespace LO.Modal

/-- Formulas of propositional modal logic. -/
inductive Formula where
  | atom   : ℕ → Formula
  | falsum : Formula
  | imp    : Formula → Formula → Formula
  | box    : Formula → Formula
  deriving DecidableEq

abbrev FormulaSet := Set Formula

abbrev FormulaFinset := Finset Formula

namespace Formula

variable {n : ℕ} {φ φ₁ φ₂ ψ ψ₁ ψ₂ : Formula}

instance : Bot Formula := ⟨falsum⟩

@[match_pattern] abbrev neg (φ : Formula) : Formula := imp φ ⊥

@[match_pattern] abbrev verum : Formula := neg ⊥

instance : Top Formula := ⟨verum⟩

@[match_pattern] abbrev or (φ ψ : Formula) : Formula := imp (neg φ) ψ

@[match_pattern] abbrev and (φ ψ : Formula) : Formula := neg (imp φ (neg ψ))

@[match_pattern] abbrev dia (φ : Formula) : Formula := neg (box (neg φ))

@[match_pattern] abbrev iff (φ ψ : Formula) : Formula := and (imp φ ψ) (imp ψ φ)

end Formula

@[inherit_doc] prefix:75 "∼" => Formula.neg
@[inherit_doc] infixr:60 " 🡒 " => Formula.imp
@[inherit_doc] infixr:69 " ⋏ " => Formula.and
@[inherit_doc] infixr:68 " ⋎ " => Formula.or
@[inherit_doc] infix:61 " 🡘 " => Formula.iff
@[inherit_doc] prefix:76 "□" => Formula.box
@[inherit_doc] prefix:76 "◇" => Formula.dia

namespace Formula

variable {n : ℕ} {φ φ₁ φ₂ ψ ψ₁ ψ₂ : Formula}

@[grind =] lemma eq_verum_neg_falsum : ⊤ = ∼(⊥ : Formula) := rfl

lemma falsum_eq : (⊥ : Formula) = falsum := rfl
lemma verum_eq : (⊤ : Formula) = verum := rfl
lemma iff_eq : φ 🡘 ψ = (φ 🡒 ψ) ⋏ (ψ 🡒 φ) := rfl
attribute [grind =_] falsum_eq verum_eq iff_eq

@[grind =] lemma inj_and : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [and]
@[grind =] lemma inj_or : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [or]
@[grind =] lemma inj_imp : φ₁ 🡒 φ₂ = ψ₁ 🡒 ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp
@[grind =] lemma inj_neg : ∼φ = ∼ψ ↔ φ = ψ := by simp [neg]
@[grind =] lemma inj_box : □φ = □ψ ↔ φ = ψ := by simp
@[grind =] lemma inj_dia : ◇φ = ◇ψ ↔ φ = ψ := by simp [dia]

/-- Formula complexity. -/
@[grind =]
def complexity : Formula → ℕ
  | atom _ => 0
  | ⊥      => 0
  | φ 🡒 ψ  => max φ.complexity ψ.complexity + 1
  | □φ     => φ.complexity + 1

@[elab_as_elim]
def cases' {C : Formula → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a, C (atom a))
    (himp : ∀ φ ψ, C (φ 🡒 ψ))
    (hbox : ∀ φ, C (□φ))
    : (φ : Formula) → C φ
  | ⊥      => hfalsum
  | atom a => hatom a
  | □φ     => hbox φ
  | φ 🡒 ψ  => himp φ ψ

@[induction_eliminator]
def rec' {C : Formula → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a, C (atom a))
    (himp : ∀ φ ψ, C φ → C ψ → C (φ 🡒 ψ))
    (hbox : ∀ φ, C φ → C (□φ))
    : (φ : Formula) → C φ
  | ⊥      => hfalsum
  | atom a => hatom a
  | φ 🡒 ψ  => himp φ ψ (rec' hfalsum hatom himp hbox φ) (rec' hfalsum hatom himp hbox ψ)
  | □φ     => hbox φ (rec' hfalsum hatom himp hbox φ)

/-- Iterated `□`. -/
abbrev multibox (n : ℕ) : Formula → Formula := (□·)^[n]

@[inherit_doc] notation:76 "□^[" n "]" φ:80 => Formula.multibox n φ

/-- Iterated `◇`. -/
abbrev multidia (n : ℕ) : Formula → Formula := (◇·)^[n]

@[inherit_doc] notation:76 "◇^[" n "]" φ:80 => Formula.multidia n φ

@[simp, grind =] lemma multibox_zero : (□^[0]φ) = φ := rfl
@[simp, grind =] lemma multibox_succ : (□^[n + 1]φ) = □(□^[n]φ) := Function.iterate_succ_apply' ..
@[simp, grind =] lemma multibox_add {m : ℕ} : (□^[n](□^[m]φ)) = □^[n + m]φ :=
  (Function.iterate_add_apply _ n m φ).symm

@[simp, grind =] lemma multidia_zero : (◇^[0]φ) = φ := rfl
@[simp, grind =] lemma multidia_succ : (◇^[n + 1]φ) = ◇(◇^[n]φ) := Function.iterate_succ_apply' ..
@[simp, grind =] lemma multidia_add {m : ℕ} : (◇^[n](◇^[m]φ)) = ◇^[n + m]φ :=
  (Function.iterate_add_apply _ n m φ).symm

end Formula

/-- A substitution of formulas for propositional variables. -/
abbrev Substitution := ℕ → Formula

/-- Simultaneous substitution of formulas for propositional variables. -/
def Formula.subst (s : Substitution) : Formula → Formula
  | atom a => s a
  | ⊥      => ⊥
  | □φ     => □(φ.subst s)
  | φ 🡒 ψ  => φ.subst s 🡒 ψ.subst s

@[inherit_doc] notation:80 φ "⟦" s "⟧" => Modal.Formula.subst s φ

namespace Formula.subst

variable {n : ℕ} {s : Substitution} {φ ψ : Formula}

lemma subst_atom {a} : (atom a)⟦s⟧ = s a := rfl
lemma subst_falsum : (⊥ : Formula)⟦s⟧ = ⊥ := rfl
lemma subst_verum : (⊤ : Formula)⟦s⟧ = ⊤ := rfl
lemma subst_imp : (φ 🡒 ψ)⟦s⟧ = φ⟦s⟧ 🡒 ψ⟦s⟧ := rfl
lemma subst_neg : (∼φ)⟦s⟧ = ∼(φ⟦s⟧) := rfl
lemma subst_and : (φ ⋏ ψ)⟦s⟧ = φ⟦s⟧ ⋏ ψ⟦s⟧ := rfl
lemma subst_or : (φ ⋎ ψ)⟦s⟧ = φ⟦s⟧ ⋎ ψ⟦s⟧ := rfl
lemma subst_iff : (φ 🡘 ψ)⟦s⟧ = (φ⟦s⟧ 🡘 ψ⟦s⟧) := rfl
attribute [simp, grind =]
  subst_atom
  subst_falsum
  subst_verum
  subst_neg
  subst_and
  subst_or
  subst_imp
  subst_iff

@[simp, grind =] lemma subst_box : (□φ)⟦s⟧ = □(φ⟦s⟧) := rfl
@[simp, grind =] lemma subst_multibox : (□^[n]φ)⟦s⟧ = □^[n](φ⟦s⟧) := by induction n <;> simp_all;
@[simp, grind =] lemma subst_dia : (◇φ)⟦s⟧ = ◇(φ⟦s⟧) := rfl
@[simp, grind =] lemma subst_multidia : (◇^[n]φ)⟦s⟧ = ◇^[n](φ⟦s⟧) := by induction n <;> simp_all;

end Formula.subst

/-- The identity substitution. -/
abbrev Substitution.id : Substitution := .atom

@[simp] lemma Formula.subst.def_id {φ : Formula} : φ⟦.id⟧ = φ := by induction φ <;> simp_all;

/-- Composition of substitutions. -/
def Substitution.comp (s₁ s₂ : Substitution) : Substitution := fun a => (s₁ a)⟦s₂⟧

@[simp]
lemma Formula.subst.def_comp {s₁ s₂ : Substitution} {φ : Formula} :
    φ⟦s₁.comp s₂⟧ = φ⟦s₁⟧⟦s₂⟧ := by
  induction φ <;> simp_all [Substitution.comp];

end LO.Modal

end
