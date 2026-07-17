module

public import Fin74.Formula.Substitution

@[expose]
public section

/-- A Kripke frame: a relation that is reflexive and transitive (the paper [Fin74] only ever
considers such frames, so this is baked into the structure rather than imposed via a separate
typeclass). No `World`/`Rel` abbreviations or `≺` notation are attached to `Frame` itself: the
relation is only ever accessed through a `Model` built on top of it, so that there is a single,
unambiguous home for the `≺` notation. -/
structure Frame (κ : Type u) where
  Rel'      : κ → κ → Prop
  rel_refl  : ∀ x, Rel' x x
  rel_trans : ∀ {x y z}, Rel' x y → Rel' y z → Rel' x z
namespace Frame

variable {F : Frame κ}


abbrev World {_ : Frame κ} := κ

abbrev Rel {F : Frame κ} : F.World → F.World → Prop := F.Rel'
infixl:60 " ≺ " => Rel

instance : IsTrans F.World F.Rel where
  trans _ _ _ := F.rel_trans
attribute [simp, grind .] Frame.rel_refl

instance : Std.Refl F.Rel where
  refl _ := F.rel_refl _
attribute [grind →] Frame.rel_trans

end Frame



/-- A Kripke model: a frame together with a valuation. -/
structure Model (κ : Type u) (α : Type v) extends Frame κ where
  Val'      : κ → α → Prop

namespace Model

variable {M : Model κ α}

abbrev Val {M : Model κ α} : M.World → α → Prop := M.Val'

end Model


namespace Model.World

variable {M : Model κ α} {x y: M.World} {A B : Formula α}

@[grind =]
def Forces (M : Model κ α) (x : M.World) : Formula α → Prop
| #a    => M.Val x a
| ⊥     => False
| A 🡒 B => Forces M x A → Forces M x B
| ◇A    => ∃ y : M.World, x ≺ y ∧ Forces _ y A
notation:80 x:50 " ⊩[" M "] " A:50 => Forces M x A
infix:50 " ⊩ " => Forces _

abbrev NotForces (M : Model κ α) (x : M.World) (A : Formula α) : Prop := ¬(x ⊩ A)
notation:80 x:50 " ⊮[" M "] " A:50 => NotForces M x A
infix:50 " ⊮ " => NotForces _

@[simp, grind .] lemma forces_top : x ⊩ ⊤ := by grind;
@[grind =] lemma forces_imp : x ⊩ A 🡒 B ↔ x ⊮ A ∨ x ⊩ B := by grind;
@[grind =] lemma forces_and : x ⊩ A ⋏ B ↔ x ⊩ A ∧ x ⊩ B := by grind;
@[grind =] lemma forces_or  : x ⊩ A ⋎ B ↔ x ⊩ A ∨ x ⊩ B := by grind;
@[grind =] lemma forces_iff : x ⊩ A 🡘 B ↔ (x ⊩ A ↔ x ⊩ B) := by grind;
@[grind =] lemma forces_neg : x ⊩ ∼A ↔ x ⊮ A := by grind;
@[grind =] lemma forces_dia : x ⊩ ◇A ↔ ∃ y : M.World, x ≺ y ∧ y ⊩ A := by grind;
@[grind =] lemma forces_box : x ⊩ □A ↔ ∀ y : M.World, x ≺ y → y ⊩ A := by grind;

@[simp, grind .] lemma not_forces_bot : x ⊮ ⊥ := by grind;
@[grind =] lemma not_forces_and : x ⊮ A ⋏ B ↔ x ⊮ A ∨ x ⊮ B := by grind;
@[grind =] lemma not_forces_or  : x ⊮ A ⋎ B ↔ x ⊮ A ∧ x ⊮ B := by grind;
@[grind =] lemma not_forces_neg : x ⊮ ∼A ↔ x ⊩ A := by grind;
@[grind =] lemma not_forces_imp : x ⊮ A 🡒 B ↔ x ⊩ A ∧ x ⊮ B := by grind;
@[grind =] lemma not_forces_dia : x ⊮ ◇A ↔ ∀ y : M.World, x ≺ y → y ⊮ A := by grind;
@[grind =] lemma not_forces_box : x ⊮ □A ↔ ∃ y : M.World, x ≺ y ∧ y ⊮ A := by grind;

/-- Boxed formulas persist along the accessibility relation. -/
@[grind →]
lemma forces_box_of_rel (h : x ⊩ □A) (hxy : x ≺ y) : y ⊩ □A := by grind;

/-- Diamond formulas pull back along the accessibility relation. -/
@[grind →]
lemma forces_dia_of_rel (h : y ⊩ ◇A) (hxy : x ≺ y) : x ⊩ ◇A := by grind;

end Model.World


namespace Model

variable {M : Model κ α} {A : Formula α}

/-- `M` satisfies `A` at every world, i.e. `A` is valid on `M`. -/
@[grind]
def Validates (M : Model κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
infix:50 " ⊧ " => Model.Validates

/-- `M` strongly verifies `A`: every uniform substitution instance of `A` is valid on `M`.
(This is the notion of "strongly verified" from [Fin74]: `A` remains valid on `M` no matter
which formulas are substituted for its atoms.) -/
@[grind]
def StronglyVerifies (M : Model κ α) (A : Formula α) : Prop := ∀ σ, M ⊧ A⟦σ⟧

end Model



namespace Frame

/-- `A` is valid on `F`: true at every world of every model built on `F`. -/
@[grind =]
def Validates (F : Frame κ) (A : Formula α) : Prop := ∀ V, (Model.mk F V) ⊧ A
infix:50 " ⊧ " => Frame.Validates

@[grind]
def ValidatesSet (F : Frame κ) (S : Set (Formula ℕ)) : Prop := ∀ A ∈ S, F.Validates A
infix:50 " ⊧ " => Frame.ValidatesSet

end Frame


end
