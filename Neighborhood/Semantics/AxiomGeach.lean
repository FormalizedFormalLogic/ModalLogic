module

public import Neighborhood.Semantics.Basic
public import Neighborhood.Axioms

/-!
# The Geach axiom family

Frame conditions dual to the Geach axiom scheme `Axioms.Geach g`: a neighborhood frame is
*Geach convergent* for parameters `g` when `◇^[g.i] (□^[g.m] X) ⊆ □^[g.j] (◇^[g.n] X)` holds for
every set of worlds `X`. Reflexivity, transitivity, seriality, symmetry and euclideanness are
each a particular instance of this scheme, dual to the axioms `T`, `Four`, `D`, `B` and `Five`
respectively.
-/

@[expose] public section

variable {κ : Type u} [Nonempty κ] {F : Frame κ} {X Y : Set κ} {g : Axioms.Geach.Taple}

namespace Frame

/-- `F` is *Geach convergent* for the parameters `g` when
`◇^[g.i] (□^[g.m] X) ⊆ □^[g.j] (◇^[g.n] X)` holds for every set of worlds `X`. -/
class IsGeachConvergent (F : Frame κ) (g : Axioms.Geach.Taple) : Prop where
  gconv : ∀ X : Set κ, F.dia^[g.i] (F.box^[g.m] X) ⊆ F.box^[g.j] (F.dia^[g.n] X)

@[simp, grind .]
lemma gconv [F.IsGeachConvergent g] : F.dia^[g.i] (F.box^[g.m] X) ⊆ F.box^[g.j] (F.dia^[g.n] X) :=
  IsGeachConvergent.gconv X

/-- `F` is reflexive: every neighborhood of a world contains it. -/
class IsReflexive (F : Frame κ) : Prop where
  refl : ∀ X : Set κ, F.box X ⊆ X

@[simp, grind .] lemma refl [F.IsReflexive] : F.box X ⊆ X := IsReflexive.refl X

@[simp, grind .]
lemma refl_dual [F.IsReflexive] : X ⊆ F.dia X := by
  intro x
  contrapose!
  intro h
  have := F.refl (X := Xᶜ)
  have := @this x
  simp_all [Frame.dia, Frame.box]

instance [F.IsReflexive] : F.IsGeachConvergent ⟨0, 0, 1, 0⟩ := ⟨by simp⟩

instance [F.IsGeachConvergent ⟨0, 0, 1, 0⟩] : F.IsReflexive := ⟨fun _ => F.gconv (g := ⟨0, 0, 1, 0⟩)⟩

/-- `F` is transitive: `□X` is closed under a further application of `□`. -/
class IsTransitive (F : Frame κ) : Prop where
  trans : ∀ X : Set κ, F.box X ⊆ F.box^[2] X

@[simp, grind .] lemma trans [F.IsTransitive] : F.box X ⊆ F.box^[2] X := IsTransitive.trans X

instance [F.IsTransitive] : F.IsGeachConvergent ⟨0, 2, 1, 0⟩ := ⟨fun _ => trans⟩

instance [F.IsGeachConvergent ⟨0, 2, 1, 0⟩] : F.IsTransitive := ⟨fun _ => F.gconv (g := ⟨0, 2, 1, 0⟩)⟩

/-- `F` is serial: every neighborhood of a world is also a neighborhood in the dual sense,
`□X ⊆ ◇X`. -/
class IsSerial (F : Frame κ) : Prop where
  serial : ∀ X : Set κ, F.box X ⊆ F.dia X

@[simp, grind .] lemma serial [F.IsSerial] : F.box X ⊆ F.dia X := IsSerial.serial X

instance [F.IsSerial] : F.IsGeachConvergent ⟨0, 0, 1, 1⟩ := ⟨by simp⟩
instance [F.IsGeachConvergent ⟨0, 0, 1, 1⟩] : F.IsSerial := ⟨fun _ => F.gconv (g := ⟨0, 0, 1, 1⟩)⟩

/-- `F` is symmetric: every world lies in `□◇X` whenever it lies in `X`. -/
class IsSymmetric (F : Frame κ) : Prop where
  symm : ∀ X : Set κ, X ⊆ F.box (F.dia X)

@[simp, grind .] lemma symm [F.IsSymmetric] : X ⊆ F.box (F.dia X) := IsSymmetric.symm X

instance [F.IsSymmetric] : F.IsGeachConvergent ⟨0, 1, 0, 1⟩ := ⟨by simp⟩
instance [F.IsGeachConvergent ⟨0, 1, 0, 1⟩] : F.IsSymmetric := ⟨fun _ => F.gconv (g := ⟨0, 1, 0, 1⟩)⟩

/-- The dual formulation of symmetry, `◇□X ⊆ X`. -/
lemma IsSymmetric.of_dual (h : ∀ X : Set κ, F.dia (F.box X) ⊆ X) : F.IsSymmetric := by
  constructor
  intro X w hw
  have := @h Xᶜ w
  simp_all [Frame.dia, Frame.box]

/-- Symmetry stated directly in terms of neighborhoods. -/
lemma IsSymmetric.of_alt (h : ∀ (X : Set κ) (a : κ), { b | Xᶜ ∉ F.𝒩 b } ∉ F.𝒩 a → a ∉ X) :
    F.IsSymmetric := by
  constructor
  intro X a ha
  have := h X a
  simp only [Frame.dia, Frame.box, Set.mem_setOf_eq] at this ⊢
  tauto

lemma iff_isSymmetric_dual : F.IsSymmetric ↔ ∀ X : Set κ, F.dia (F.box X) ⊆ X := by
  constructor
  · intro h X w
    have := @h.symm (X := Xᶜ) w
    simp_all [Frame.dia, Frame.box]
    tauto
  · intro h; exact IsSymmetric.of_dual h

/-- `F` is euclidean: `◇X ⊆ □◇X`. -/
class IsEuclidean (F : Frame κ) : Prop where
  eucl : ∀ X : Set κ, F.dia X ⊆ F.box (F.dia X)

@[simp, grind .] lemma eucl [F.IsEuclidean] : F.dia X ⊆ F.box (F.dia X) := IsEuclidean.eucl X

@[simp, grind .]
lemma eucl_dual [F.IsEuclidean] : F.dia (F.box X) ⊆ F.box X := by
  intro x
  contrapose!
  intro h
  have := F.eucl (X := Xᶜ)
  have := @this x
  simp_all [Frame.dia, Frame.box]

/-- The dual formulation of euclideanness, `◇□X ⊆ □X`. -/
lemma IsEuclidean.of_dual (h : ∀ X : Set κ, F.dia (F.box X) ⊆ F.box X) : F.IsEuclidean := by
  constructor
  intro X w hw
  have := @h Xᶜ w
  simp_all [Frame.dia, Frame.box]

/-- Euclideanness stated directly in terms of neighborhoods. -/
lemma IsEuclidean.of_alt (h : ∀ (X : Set κ) (a : κ), X ∉ F.𝒩 a → { b | X ∉ F.𝒩 b } ∈ F.𝒩 a) :
    F.IsEuclidean := by
  constructor
  intro X a ha
  have := h Xᶜ a
  simp only [Frame.dia, Frame.box, Set.mem_setOf_eq, Set.mem_compl_iff] at ha this ⊢
  tauto

instance [F.IsEuclidean] : F.IsGeachConvergent ⟨1, 1, 0, 1⟩ := ⟨by simp⟩
instance [F.IsGeachConvergent ⟨1, 1, 0, 1⟩] : F.IsEuclidean := ⟨fun _ => F.gconv (g := ⟨1, 1, 0, 1⟩)⟩

end Frame

section

variable {α : Type v} {A : Formula α}

/-- The Geach axiom scheme is valid on any Geach convergent frame, for every formula. -/
theorem valid_axiomGeach_of_isGeachConvergent (g : Axioms.Geach.Taple) [F.IsGeachConvergent g] :
    F ⊧ Axioms.Geach g A := by
  intro V x
  simp only [forces_imp, forces_diaItr, forces_boxItr, Model.truthset.eq_boxItr,
    Model.truthset.eq_diaItr]
  apply F.gconv

@[simp, grind .]
theorem valid_axiomT_of_isReflexive [F.IsReflexive] : F ⊧ Axioms.T A :=
  valid_axiomGeach_of_isGeachConvergent ⟨0, 0, 1, 0⟩

@[simp, grind .]
theorem valid_axiomD_of_isSerial [F.IsSerial] : F ⊧ Axioms.D A :=
  valid_axiomGeach_of_isGeachConvergent ⟨0, 0, 1, 1⟩

@[simp, grind .]
theorem valid_axiomB_of_isSymmetric [F.IsSymmetric] : F ⊧ Axioms.B A :=
  valid_axiomGeach_of_isGeachConvergent ⟨0, 1, 0, 1⟩

@[simp, grind .]
theorem valid_axiomFour_of_isTransitive [F.IsTransitive] : F ⊧ Axioms.Four A :=
  valid_axiomGeach_of_isGeachConvergent ⟨0, 2, 1, 0⟩

@[simp, grind .]
theorem valid_axiomFive_of_isEuclidean [F.IsEuclidean] : F ⊧ Axioms.Five A :=
  valid_axiomGeach_of_isGeachConvergent ⟨1, 1, 0, 1⟩

end

section

variable {a : ℕ}

/-- If `Axioms.Geach g` is valid on `F` for some atom, `F` is Geach convergent for `g`. -/
theorem isGeachConvergent_of_valid_axiomGeach (h : F ⊧ Axioms.Geach g (.atom a)) :
    F.IsGeachConvergent g := by
  refine ⟨fun X x hx => ?_⟩
  have : x ∈ F.dia^[g.i] (F.box^[g.m] X) → x ∈ F.box^[g.j] (F.dia^[g.n] X) := by
    simpa [forces_imp, forces_diaItr, forces_boxItr] using h (fun _ => X) x
  exact this hx

theorem isReflexive_of_valid_axiomT (h : F ⊧ Axioms.T (.atom a)) : F.IsReflexive := by
  have := isGeachConvergent_of_valid_axiomGeach (g := ⟨0, 0, 1, 0⟩) h
  infer_instance

theorem isTransitive_of_valid_axiomFour (h : F ⊧ Axioms.Four (.atom a)) : F.IsTransitive := by
  have := isGeachConvergent_of_valid_axiomGeach (g := ⟨0, 2, 1, 0⟩) h
  infer_instance

theorem isSerial_of_valid_axiomD (h : F ⊧ Axioms.D (.atom a)) : F.IsSerial := by
  have := isGeachConvergent_of_valid_axiomGeach (g := ⟨0, 0, 1, 1⟩) h
  infer_instance

theorem isSymmetric_of_valid_axiomB (h : F ⊧ Axioms.B (.atom a)) : F.IsSymmetric := by
  have := isGeachConvergent_of_valid_axiomGeach (g := ⟨0, 1, 0, 1⟩) h
  infer_instance

theorem isEuclidean_of_valid_axiomFive (h : F ⊧ Axioms.Five (.atom a)) : F.IsEuclidean := by
  have := isGeachConvergent_of_valid_axiomGeach (g := ⟨1, 1, 0, 1⟩) h
  infer_instance

end

end
