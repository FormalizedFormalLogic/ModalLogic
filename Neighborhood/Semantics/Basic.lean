module

public import Neighborhood.Formula.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Finite.Defs
public import Mathlib.Tactic.TautoSet

/-!
# Neighborhood semantics

Basic definitions of neighborhood frames and models for propositional modal logic, together
with the associated notions of forcing, truth sets, and validity.

A neighborhood frame assigns to every world `x` a set `𝒩 x` of subsets of the carrier (its
*neighborhoods*); the formula `□A` is forced at `x` exactly when the truth set of `A` is one of
these neighborhoods. A neighborhood model additionally carries a valuation of the propositional
variables.
-/

@[expose] public section

/-- A neighborhood frame on a nonempty carrier `κ`: to every world `x : κ` it assigns a set
`𝒩 x` of subsets of `κ`, its neighborhoods. -/
structure Frame (κ : Type u) [Nonempty κ] where
  𝒩 : κ → Set (Set κ)

namespace Frame

variable {κ : Type u} [Nonempty κ] {α : Type v}

/-- The carrier of a frame, exposed as `F.World` so that a binder `x : F.World` keeps `F` fixed
during elaboration. -/
abbrev World (_ : Frame κ) := κ

variable {F : Frame κ} {X Y : Set κ}

/-- The set of worlds `x` for which `X` is a neighborhood, i.e. the interpretation of `□` on
truth sets. -/
def box (F : Frame κ) : Set κ → Set κ := fun X => { x | X ∈ F.𝒩 x }

/-- The interpretation of `◇` on truth sets, dual to `box`. -/
def dia (F : Frame κ) : Set κ → Set κ := fun X => (F.box Xᶜ)ᶜ

lemma eq_ℬ_𝒩 : F.box X = Y ↔ ∀ x, X ∈ F.𝒩 x ↔ x ∈ Y := by
  constructor
  · rintro rfl; tauto
  · intro h; ext x; exact h x

/-- The frame with carrier `κ` whose box operator is `B`. -/
def mk_ℬ (B : Set κ → Set κ) : Frame κ := ⟨fun x => { X | x ∈ B X }⟩

/-- A frame with finitely many worlds. -/
class IsFinite (F : Frame κ) : Prop where
  world_finite : Finite F.World

/-- The one-world frame whose only neighborhood is the whole carrier. -/
abbrev simple_blackhole : Frame Unit := ⟨fun _ => { Set.univ }⟩

end Frame

/-- A neighborhood model: a frame together with a valuation of the propositional variables. -/
structure Model (κ : Type u) [Nonempty κ] (α : Type v) extends Frame κ where
  Val : α → Set κ

/-- The truth set of a formula in a model: the set of worlds at which it is forced. -/
@[grind]
def Model.truthset {κ : Type u} [Nonempty κ] {α : Type v} (M : Model κ α) : Formula α → Set κ
  | .atom a => M.Val a
  | ⊥       => ∅
  | A 🡒 B  => (Model.truthset M A)ᶜ ∪ Model.truthset M B
  | □A      => M.box (Model.truthset M A)

instance {κ : Type u} [Nonempty κ] {α : Type v} : CoeFun (Model κ α) (fun M => Formula α → Set M.World) :=
  ⟨Model.truthset⟩

namespace Model.truthset

variable {κ : Type u} [Nonempty κ] {α : Type v} {M : Model κ α} {a : α} {A B : Formula α} {n : ℕ}

@[simp, grind =] lemma eq_atom : M (.atom a) = M.Val a := rfl
@[simp, grind =] lemma eq_bot  : M (⊥ : Formula α) = ∅ := rfl
@[simp, grind =] lemma eq_top  : M (⊤ : Formula α) = Set.univ := by simp [Model.truthset]
@[simp, grind =] lemma eq_imp  : M (A 🡒 B) = (M A)ᶜ ∪ M B := rfl
@[simp, grind =] lemma eq_neg  : M (∼A) = (M A)ᶜ := by simp [Model.truthset]
@[simp, grind =] lemma eq_and  : M (A ⋏ B) = M A ∩ M B := by simp [Model.truthset]
@[simp, grind =] lemma eq_or   : M (A ⋎ B) = M A ∪ M B := by simp [Model.truthset]
@[simp, grind =] lemma eq_iff  : M (A 🡘 B) = (M A ∩ M B) ∪ ((M A)ᶜ ∩ (M B)ᶜ) := by
  simp [Model.truthset]; tauto_set
@[simp, grind =] lemma eq_box  : M (□A) = M.box (M A) := rfl
@[simp, grind =] lemma eq_dia  : M (◇A) = M.dia (M A) := by simp [Frame.dia, Model.truthset]

@[simp, grind =]
lemma eq_boxItr : M (□^[n]A) = M.box^[n] (M A) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ']; simp [ih]

@[simp, grind =]
lemma eq_diaItr : M (◇^[n]A) = M.dia^[n] (M A) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ']; simp [ih, Frame.dia]

end Model.truthset

/-- `x` forces `A` in the model to which `x` belongs, i.e. `x` lies in the truth set of `A`. -/
@[grind]
def Forces {κ : Type u} [Nonempty κ] {α : Type v} {M : Model κ α} (x : M.World) (A : Formula α) : Prop :=
  x ∈ M.truthset A
@[inherit_doc] infix:55 " ⊩ " => Forces

/-- `x` does not force `A`. -/
abbrev NotForces {κ : Type u} [Nonempty κ] {α : Type v} {M : Model κ α} (x : M.World) (A : Formula α) : Prop :=
  ¬x ⊩ A
@[inherit_doc] infix:55 " ⊮ " => NotForces

section

variable {κ : Type u} [Nonempty κ] {α : Type v} {M : Model κ α} {x : M.World} {a : α} {A B : Formula α} {n : ℕ}

@[simp, grind .] lemma forces_top : x ⊩ (⊤ : Formula α) := by simp [Forces]
@[simp, grind .] lemma not_forces_bot : x ⊮ (⊥ : Formula α) := by simp [NotForces, Forces]
@[grind =] lemma forces_atom : x ⊩ (.atom a) ↔ x ∈ M.Val a := by simp [Forces]
@[grind =] lemma forces_neg : x ⊩ ∼A ↔ x ⊮ A := by simp [NotForces, Forces]
@[grind =] lemma forces_imp : x ⊩ A 🡒 B ↔ (x ⊩ A → x ⊩ B) := by simp [Forces]; tauto
@[grind =] lemma forces_and : x ⊩ A ⋏ B ↔ x ⊩ A ∧ x ⊩ B := by simp [Forces]
@[grind =] lemma forces_or  : x ⊩ A ⋎ B ↔ x ⊩ A ∨ x ⊩ B := by simp [Forces]
@[grind =] lemma forces_iff : x ⊩ A 🡘 B ↔ (x ⊩ A ↔ x ⊩ B) := by simp [Forces]; tauto
@[grind =] lemma forces_box : x ⊩ □A ↔ x ∈ M.box (M.truthset A) := by simp [Forces]
@[grind =] lemma forces_dia : x ⊩ ◇A ↔ x ∈ M.dia (M.truthset A) := by simp [Forces, Frame.dia]
@[grind =] lemma forces_boxItr : x ⊩ □^[n]A ↔ x ∈ M.box^[n] (M.truthset A) := by simp [Forces]
@[grind =] lemma forces_diaItr : x ⊩ ◇^[n]A ↔ x ∈ M.dia^[n] (M.truthset A) := by simp [Forces]

end

/-- A formula is valid on a model when every world forces it. -/
@[grind]
def Model.Validate {κ : Type u} [Nonempty κ] {α : Type v} (M : Model κ α) (A : Formula α) : Prop :=
  ∀ x : M.World, x ⊩ A
@[inherit_doc] infix:50 " ⊧ " => Model.Validate

theorem valid_iff {κ : Type u} [Nonempty κ] {α : Type v} {M : Model κ α} {A B : Formula α} :
    M ⊧ A 🡘 B ↔ M.truthset A = M.truthset B := by
  constructor
  · intro h; ext x; exact forces_iff.mp (h x)
  · intro h x
    apply forces_iff.mpr
    show x ∈ M.truthset A ↔ x ∈ M.truthset B
    rw [h]

theorem Model.Validate.mdp {κ : Type u} [Nonempty κ] {α : Type v} {M : Model κ α} {A B : Formula α}
    (hAB : M ⊧ A 🡒 B) (hA : M ⊧ A) : M ⊧ B := fun x => (forces_imp.mp (hAB x)) (hA x)

theorem Model.Validate.re {κ : Type u} [Nonempty κ] {α : Type v} {M : Model κ α} {A B : Formula α}
    (h : M ⊧ A 🡘 B) : M ⊧ □A 🡘 □B := by
  rw [valid_iff] at h ⊢
  simp [h]

/-- A formula is valid on a frame when it is valid on every model built on that frame. -/
@[grind]
def Frame.Validate {κ : Type u} [Nonempty κ] {α : Type v} (F : Frame κ) (A : Formula α) : Prop :=
  ∀ V : α → Set κ, (⟨F, V⟩ : Model κ α) ⊧ A
@[inherit_doc] infix:50 " ⊧ " => Frame.Validate

theorem Frame.Validate.mdp {κ : Type u} [Nonempty κ] {α : Type v} {F : Frame κ} {A B : Formula α}
    (hAB : F ⊧ A 🡒 B) (hA : F ⊧ A) : F ⊧ B := fun V => Model.Validate.mdp (hAB V) (hA V)

theorem Frame.Validate.re {κ : Type u} [Nonempty κ] {α : Type v} {F : Frame κ} {A B : Formula α}
    (h : F ⊧ A 🡘 B) : F ⊧ □A 🡘 □B := fun V => Model.Validate.re (h V)

theorem Frame.Validate.not_bot {κ : Type u} [Nonempty κ] {α : Type v} (F : Frame κ) :
    ¬F ⊧ (⊥ : Formula α) := by
  intro h
  have := h (fun _ => (∅ : Set κ)) (Classical.arbitrary κ)
  simp [Forces] at this

theorem Frame.Validate.iff_not_exists_valuation_world
    {κ : Type u} [Nonempty κ] {α : Type v} {F : Frame κ} {A : Formula α} :
    ¬F ⊧ A ↔ ∃ V : α → Set κ, ∃ x : (⟨F, V⟩ : Model κ α).World, x ⊮ A := by
  simp [Frame.Validate, Model.Validate, Forces, NotForces]

alias ⟨Frame.Validate.exists_valuation_world_of_not, Frame.Validate.not_of_exists_valuation_world⟩ :=
  Frame.Validate.iff_not_exists_valuation_world

end
