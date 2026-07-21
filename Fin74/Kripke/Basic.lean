module

public import Fin74.Formula.Substitution

@[expose]
public section

/-- A Kripke frame: a relation that is reflexive and transitive.

- [Fin74] -/
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

@[grind →]
lemma forces_box_of_rel (h : x ⊩ □A) (hxy : x ≺ y) : y ⊩ □A := by grind;

@[grind →]
lemma forces_dia_of_rel (h : y ⊩ ◇A) (hxy : x ≺ y) : x ⊩ ◇A := by grind;

@[grind =]
lemma forces_subst {M : Model κ β} {x : M.World} {σ : Formula.Substitution α β} {A : Formula α} :
    x ⊩[M] A⟦σ⟧ ↔ x ⊩[⟨M.toFrame, fun w a => w ⊩[M] σ a⟩] A := by
  induction A generalizing x with
  | atom a => rfl
  | bot => rfl
  | imp A B ihA ihB => grind
  | dia A ih => grind

end Model.World


namespace Model

variable {M : Model κ α} {A : Formula α}

@[grind]
def Validates (M : Model κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
infix:50 " ⊧ " => Model.Validates

/-- `M` strongly verifies `A`: every uniform substitution instance of `A` is valid on `M`.

- [Fin74] -/
@[grind]
def StronglyVerifies (M : Model κ α) (A : Formula α) : Prop := ∀ σ, M ⊧ A⟦σ⟧

end Model



namespace Frame

@[grind =]
def Validates (F : Frame κ) (A : Formula α) : Prop := ∀ V, (Model.mk F V) ⊧ A
infix:50 " ⊧ " => Frame.Validates

@[grind]
def ValidatesSet (F : Frame κ) (S : Set (Formula ℕ)) : Prop := ∀ A ∈ S, F.Validates A
infix:50 " ⊧ " => Frame.ValidatesSet

lemma forces_subst_of_validates {F : Frame κ} {A : Formula α} {σ : Formula.Substitution α α}
    (h : F.Validates A) : F.Validates (A⟦σ⟧) := by
  intro V x;
  exact Model.World.forces_subst.mpr (h (fun w a => w ⊩[⟨F, V⟩] σ a) x)

end Frame

namespace Model

lemma stronglyVerifies_of_frame_validates {F : Frame κ} {A : Formula α} (h : F.Validates A)
    (V) : Model.StronglyVerifies ⟨F, V⟩ A := by
  intro σ x;
  exact Frame.forces_subst_of_validates h V x

end Model


end
