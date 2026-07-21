module

public import Fin74.Formula.Basic

@[expose]
public section

namespace Formula

variable {α β γ : Type*}

abbrev Substitution (α β) := α → Formula β

/-- Uniform substitution of atoms, extended homomorphically over `⊥`/`🡒`/`◇`. -/
@[grind =]
def subst (s : Substitution α β) : Formula α → Formula β
| #a    => s a
| ⊥     => ⊥
| A 🡒 B => subst s A 🡒 subst s B
| ◇A    => ◇(subst s A)
notation:95 A "⟦" s "⟧" => Formula.subst s A

variable {s : Substitution α β} {A B : Formula α}

@[simp, grind =] lemma subst_atom {a : α} : (#a)⟦s⟧ = s a := rfl
@[simp, grind =] lemma subst_bot : (⊥ : Formula α)⟦s⟧ = ⊥ := rfl
@[simp, grind =] lemma subst_imp : (A 🡒 B)⟦s⟧ = A⟦s⟧ 🡒 B⟦s⟧ := rfl
@[simp, grind =] lemma subst_dia : (◇A)⟦s⟧ = ◇(A⟦s⟧) := rfl

@[simp, grind =] lemma subst_neg : (∼A)⟦s⟧ = ∼(A⟦s⟧) := rfl
@[simp, grind =] lemma subst_or : (A ⋎ B)⟦s⟧ = A⟦s⟧ ⋎ B⟦s⟧ := rfl
@[simp, grind =] lemma subst_and : (A ⋏ B)⟦s⟧ = A⟦s⟧ ⋏ B⟦s⟧ := rfl
@[simp, grind =] lemma subst_iff : (A 🡘 B)⟦s⟧ = A⟦s⟧ 🡘 B⟦s⟧ := rfl
@[simp, grind =] lemma subst_top : (⊤ : Formula α)⟦s⟧ = ⊤ := rfl
@[simp, grind =] lemma subst_box : (□A)⟦s⟧ = □(A⟦s⟧) := rfl

@[grind =]
lemma subst_subst {t : Substitution α β} {s : Substitution β γ} {A : Formula α} :
    (A⟦t⟧)⟦s⟧ = A⟦fun a => (t a)⟦s⟧⟧ := by
  induction A with
  | atom a => rfl
  | bot => rfl
  | imp A B ihA ihB => simp [subst, ihA, ihB]
  | dia A ih => simp [subst, ih]

@[simp, grind =]
lemma subst_id {A : Formula α} : A⟦(#·)⟧ = A := by
  induction A with
  | atom a => rfl
  | bot => rfl
  | imp A B ihA ihB => simp [subst, ihA, ihB]
  | dia A ih => simp [subst, ih]

end Formula

end
