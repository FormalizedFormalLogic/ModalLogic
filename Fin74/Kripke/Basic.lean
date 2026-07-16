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

/-- A Kripke model: a frame together with a valuation. -/
structure Model (κ : Type u) (α : Type v) extends Frame κ where
  Val'      : κ → α → Prop

instance : CoeFun (Model κ α) (fun _ => κ → α → Prop) := ⟨Model.Val'⟩

/-- The model on frame `F` with valuation `V`. -/
def Frame.model (F : Frame κ) (V : κ → α → Prop) : Model κ α := { toFrame := F, Val' := V }

@[simp, grind =] lemma Frame.model_toFrame (F : Frame κ) (V : κ → α → Prop) :
    (F.model V).toFrame = F := rfl

@[simp, grind =] lemma Frame.model_rel (F : Frame κ) (V : κ → α → Prop) :
    (F.model V).Rel' = F.Rel' := rfl

@[simp, grind =] lemma Frame.model_val (F : Frame κ) (V : κ → α → Prop) :
    (F.model V).Val' = V := rfl

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

/-- Model-explicit forcing: `x ⊩[M] A` forces the model `M` to be pinned down by name rather
than inferred from the type of `x`. Needed for raw points `x : κ` (e.g. along a chain `u : ℕ →
κ`) that are not already tied to a specific model via their type, since `M.World` is
definitionally just `κ` and so carries no information to unify `M` against.

(Implemented as a `macro` rather than a plain `notation`: with `notation`, an unannotated `M`
slot only parses at atom precedence, so a compound term like `F.model V` in the brackets fails
to elaborate; `macro` lets us pick the term precedence for `M` explicitly.) -/
macro:55 x:term:56 " ⊩[" M:term:51 "] " A:term:56 : term =>
  `(Model.World.Forces (M := $M) $x $A)

/-- Model-explicit non-forcing, dual to `⊩[M]`. -/
macro:55 x:term:56 " ⊮[" M:term:51 "] " A:term:56 : term =>
  `(¬ Model.World.Forces (M := $M) $x $A)

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

/-- Boxed formulas persist along the accessibility relation. -/
@[grind →]
lemma forces_box_of_rel {y : M.World} (h : x ⊩ □A) (hxy : x ≺ y) : y ⊩ □A := by grind;

/-- Diamond formulas pull back along the accessibility relation. -/
@[grind →]
lemma forces_dia_of_rel {y : M.World} (h : y ⊩ ◇A) (hxy : x ≺ y) : x ⊩ ◇A := by grind;

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

/-- `M` with its valuation replaced by `V`, keeping the same underlying frame `M.toFrame`
(relation, reflexivity, transitivity). -/
@[grind =]
def setVal (M : Model κ α) (V : κ → α → Prop) : Model κ α := M.toFrame.model V

@[simp, grind =] lemma setVal_rel (M : Model κ α) (V : κ → α → Prop) : (M.setVal V).Rel' = M.Rel' := rfl
@[simp, grind =] lemma setVal_val (M : Model κ α) (V : κ → α → Prop) : (M.setVal V).Val' = V := rfl

end Model

/-- `A` is valid on `F`: true at every world of every model built on `F`. -/
@[grind =]
def Frame.Validates (F : Frame κ) (A : Formula α) : Prop := ∀ V : κ → α → Prop, F.model V ⊧ A

def Frame.ValidatesSet (F : Frame κ) (S : Set (Formula ℕ)) : Prop := ∀ A ∈ S, F.Validates A
infix:50 " ⊧ " => Frame.ValidatesSet

namespace Model

variable {M : Model κ α} {A : Formula α}

/-- `A` is valid on the frame underlying `M`: true at every world of every model obtained
from `M` by only changing the valuation. This is `M.toFrame.Validates A` in disguise, kept
around under its original name so that existing call sites do not need to change. -/
@[grind =]
def FrameValidates (M : Model κ α) (A : Formula α) : Prop := M.toFrame.Validates A

end Model

end
