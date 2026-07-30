module

public import Neighborhood.Semantics.Basic
public import Neighborhood.Semantics.Completeness
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

section

variable {α : Type u} {L : Logic α} [DecidableEq α] [L.Cl] [L.HasRE] [Nonempty (MaximalConsistentSet L)]

namespace Logic

variable {A B : Formula α}

omit [DecidableEq α] [L.HasRE] [Nonempty (MaximalConsistentSet L)] in
private lemma not_iff_not_of_iff (h : A 🡘 B ∈ L) : ∼A 🡘 ∼B ∈ L :=
  E_intro (contra (C_of_E_mpr h)) (contra (C_of_E_mp h))

omit [DecidableEq α] [Nonempty (MaximalConsistentSet L)] in
private lemma dia_congr (h : A 🡘 B ∈ L) : ◇A 🡘 ◇B ∈ L :=
  not_iff_not_of_iff (re (not_iff_not_of_iff h))

omit [DecidableEq α] [Nonempty (MaximalConsistentSet L)] in
private lemma multidia_congr (h : A 🡘 B ∈ L) (n : ℕ) : ◇^[n]A 🡘 ◇^[n]B ∈ L := by
  induction n with
  | zero => simpa
  | succ n ih => simpa using dia_congr ih

omit [DecidableEq α] [Nonempty (MaximalConsistentSet L)] in
private lemma neg_box_iff_dia_neg (A : Formula α) : ∼(□A) 🡘 ◇(∼A) ∈ L :=
  not_iff_not_of_iff (re (E_intro dni dne))

omit [DecidableEq α] [L.HasRE] [Nonempty (MaximalConsistentSet L)] in
private lemma neg_dia_iff_box_neg (A : Formula α) : ∼(◇A) 🡘 □(∼A) ∈ L := E_intro dne dni

omit [DecidableEq α] [Nonempty (MaximalConsistentSet L)] in
private lemma neg_boxItr_iff_diaItr_neg (n : ℕ) (A : Formula α) :
    ∼(□^[n]A) 🡘 ◇^[n](∼A) ∈ L := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Formula.multibox_succ, Formula.multidia_succ]
    exact E_trans (neg_box_iff_dia_neg _) (dia_congr ih)

omit [DecidableEq α] [Nonempty (MaximalConsistentSet L)] in
private lemma neg_diaItr_iff_boxItr_neg (n : ℕ) (A : Formula α) :
    ∼(◇^[n]A) 🡘 □^[n](∼A) ∈ L := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Formula.multidia_succ, Formula.multibox_succ]
    exact E_trans (neg_dia_iff_box_neg _) (re ih)

omit [DecidableEq α] [Nonempty (MaximalConsistentSet L)] in
/-- The dual of a boxed-then-diamonded negated formula: pure contraposition and `RE`-congruence,
without any further modal assumption on `L`. -/
private lemma neg_boxItr_diaItr_neg (i n : ℕ) (A : Formula α) :
    ∼(□^[i](◇^[n](∼A))) 🡘 ◇^[i](□^[n]A) ∈ L := by
  have h2 : ∼(◇^[n](∼A)) 🡘 □^[n]A ∈ L :=
    E_trans (neg_diaItr_iff_boxItr_neg n (∼A)) (multire (E_intro dne dni))
  exact E_trans (neg_boxItr_iff_diaItr_neg i _) (multidia_congr h2 i)

omit [DecidableEq α] [Nonempty (MaximalConsistentSet L)] in
/-- The dual of a diamonded-then-boxed negated formula, symmetric to
`neg_boxItr_diaItr_neg`. -/
private lemma neg_diaItr_boxItr_neg (i n : ℕ) (A : Formula α) :
    ∼(◇^[i](□^[n](∼A))) 🡘 □^[i](◇^[n]A) ∈ L := by
  have h2 : ∼(□^[n](∼A)) 🡘 ◇^[n]A ∈ L :=
    E_trans (neg_boxItr_iff_diaItr_neg n (∼A)) (multidia_congr (E_intro dne dni) n)
  exact E_trans (neg_diaItr_iff_boxItr_neg i _) (multire (n := i) h2)

/-- The Geach axiom scheme is closed under swapping `i ↔ j` and `m ↔ n`: this is the purely
propositional contrapositive of the scheme, so it holds regardless of the ambient modal axioms.

Stated as a `def` rather than an `instance`: the swapped tuple's fields are projections of the
implicit `g`, so instance search cannot invert them to find `g` from the goal and this must be
applied explicitly with `g` provided. -/
@[reducible] def hasAxiomGeachSwap {g : Axioms.Geach.Taple} [L.HasAxiomGeach g] :
    L.HasAxiomGeach ⟨g.j, g.i, g.n, g.m⟩ where
  Geach A := by
    have h : Axioms.Geach g (∼A) ∈ L := axiomGeach
    have hc : ∼(□^[g.j](◇^[g.n](∼A))) 🡒 ∼(◇^[g.i](□^[g.m](∼A))) ∈ L := contra h
    have e1 : ∼(□^[g.j](◇^[g.n](∼A))) 🡘 ◇^[g.j](□^[g.n]A) ∈ L := neg_boxItr_diaItr_neg g.j g.n A
    have e2 : ∼(◇^[g.i](□^[g.m](∼A))) 🡘 □^[g.i](◇^[g.m]A) ∈ L := neg_diaItr_boxItr_neg g.i g.m A
    exact C_trans (C_of_E_mpr e1) (C_trans hc (C_of_E_mp e2))

end Logic

namespace Canonicity

variable {𝓒 : Canonicity L}

/-- A sufficient condition for `𝓒.toModel` to be Geach convergent for `g`: the convergence
inclusion holds on every neighborhood witnessing a non-proofset, the case of a proofset following
automatically from the Geach axiom scheme. -/
@[reducible] protected def isGeachean (g : Axioms.Geach.Taple) [L.HasAxiomGeach g]
    (h : ∀ X : Proofset L, X.IsNonproofset →
      𝓒.toModel.dia^[g.i] (𝓒.toModel.box^[g.m] X) ⊆ 𝓒.toModel.box^[g.j] (𝓒.toModel.dia^[g.n] X)) :
    𝓒.toModel.IsGeachConvergent g := by
  constructor
  intro X Ω hX
  by_cases X_np : Proofset.IsNonproofset X
  · exact h X X_np hX
  · obtain ⟨A, rfl⟩ := iff_not_isNonproofset_exists.mp X_np
    replace hX : Ω ∈ proofset L (◇^[g.i](□^[g.m]A)) := by
      simpa only [Canonicity.diaItr_proofset, Canonicity.boxItr_proofset] using hX
    suffices Ω ∈ proofset L (□^[g.j](◇^[g.n]A)) by simpa
    exact MaximalConsistentSet.mdp_provable (by simp) hX

@[reducible] def isReflexive [L.HasAxiomT]
    (h : ∀ X : Proofset L, X.IsNonproofset → 𝓒.toModel.box X ⊆ X) : 𝓒.toModel.IsReflexive := by
  have := Canonicity.isGeachean ⟨0, 0, 1, 0⟩ h
  infer_instance

@[reducible] def isTransitive [L.HasAxiomFour]
    (h : ∀ X : Proofset L, X.IsNonproofset → 𝓒.toModel.box X ⊆ 𝓒.toModel.box^[2] X) :
    𝓒.toModel.IsTransitive := by
  have := Canonicity.isGeachean ⟨0, 2, 1, 0⟩ h
  infer_instance

@[reducible] def isSerial [L.HasAxiomD]
    (h : ∀ X : Proofset L, X.IsNonproofset → 𝓒.toModel.box X ⊆ 𝓒.toModel.dia X) :
    𝓒.toModel.IsSerial := by
  have := Canonicity.isGeachean ⟨0, 0, 1, 1⟩ h
  infer_instance

@[reducible] def isEuclidean [L.HasAxiomFive]
    (h : ∀ X : Proofset L, X.IsNonproofset →
      𝓒.toModel.dia X ⊆ 𝓒.toModel.box (𝓒.toModel.dia X)) : 𝓒.toModel.IsEuclidean := by
  have := Canonicity.isGeachean ⟨1, 1, 0, 1⟩ h
  infer_instance

@[reducible] def isEuclidean' [L.HasAxiomFive]
    (h : ∀ X : Proofset L, X.IsNonproofset →
      𝓒.toModel.dia (𝓒.toModel.box X) ⊆ 𝓒.toModel.box X) : 𝓒.toModel.IsEuclidean := by
  haveI := Logic.hasAxiomGeachSwap (L := L) (g := ⟨1, 1, 0, 1⟩)
  apply Frame.IsEuclidean.of_dual
  apply (Canonicity.isGeachean ⟨1, 1, 1, 0⟩ h).gconv

@[reducible] def isSymmetric [L.HasAxiomB]
    (h : ∀ X : Proofset L, X.IsNonproofset → X ⊆ 𝓒.toModel.box (𝓒.toModel.dia X)) :
    𝓒.toModel.IsSymmetric := by
  have := Canonicity.isGeachean ⟨0, 1, 0, 1⟩ h
  infer_instance

@[reducible] def isSymmetric' [L.HasAxiomB]
    (h : ∀ X : Proofset L, X.IsNonproofset → 𝓒.toModel.dia (𝓒.toModel.box X) ⊆ X) :
    𝓒.toModel.IsSymmetric := by
  haveI := Logic.hasAxiomGeachSwap (L := L) (g := ⟨0, 1, 0, 1⟩)
  apply Frame.IsSymmetric.of_dual
  apply (Canonicity.isGeachean ⟨1, 0, 1, 0⟩ h).gconv

end Canonicity

instance [L.HasAxiomT] : (basicCanonicity L).toModel.IsReflexive := by
  apply Canonicity.isReflexive
  intro X hX Ω hΩ
  obtain ⟨A, rfl, hA⟩ := basicCanonicity.iff_mem_box_exists_fml.mp hΩ
  exact proofset.imp_subset.mp Logic.axiomT hA

instance [L.HasAxiomFour] : (basicCanonicity L).toModel.IsTransitive := by
  apply Canonicity.isTransitive
  intro X hX Ω hΩ
  obtain ⟨A, rfl, hA⟩ := basicCanonicity.iff_mem_box_exists_fml.mp hΩ
  simp only [Canonicity.boxItr_proofset]
  exact proofset.imp_subset.mp Logic.axiomFour hA

instance [L.HasAxiomD] : (basicCanonicity L).toModel.IsSerial := by
  apply Canonicity.isSerial
  intro X hX Ω hΩ
  obtain ⟨A, rfl, hA⟩ := basicCanonicity.iff_mem_box_exists_fml.mp hΩ
  simp only [Canonicity.dia_proofset]
  exact proofset.imp_subset.mp Logic.axiomD hA

namespace relativeBasicCanonicity

variable {P : MaximalConsistentSet L → Set (Proofset L)}

@[reducible] protected def isSerial [L.HasAxiomD]
    (hP : ∀ X : Proofset L, X.IsNonproofset → ∀ Ω, X ∈ P Ω →
      Ω ∈ (relativeBasicCanonicity L P).toModel.dia X) :
    (relativeBasicCanonicity L P).toModel.IsSerial := by
  apply Canonicity.isSerial
  intro X hX Ω hΩ
  apply hP X hX
  rcases hΩ with (h | ⟨_, h⟩)
  · exact absurd hX (basicCanonicity.not_isNonproofset_of_mem_box h)
  · exact h

@[reducible] protected def isReflexive [L.HasAxiomT]
    (hP : ∀ X : Proofset L, X.IsNonproofset → ∀ Ω, X ∈ P Ω → Ω ∈ X) :
    (relativeBasicCanonicity L P).toModel.IsReflexive := by
  apply Canonicity.isReflexive
  intro X hX Ω hΩ
  apply hP X hX
  rcases hΩ with (h | ⟨_, h⟩)
  · exact absurd hX (basicCanonicity.not_isNonproofset_of_mem_box h)
  · exact h

@[reducible] protected def isTransitive [L.HasAxiomFour]
    (hP : ∀ X : Proofset L, X.IsNonproofset → ∀ Ω, X ∈ P Ω →
      Ω ∈ (relativeBasicCanonicity L P).toModel.box^[2] X) :
    (relativeBasicCanonicity L P).toModel.IsTransitive := by
  apply Canonicity.isTransitive
  intro X hX Ω hΩ
  apply hP X hX
  rcases hΩ with (h | ⟨_, h⟩)
  · exact absurd hX (basicCanonicity.not_isNonproofset_of_mem_box h)
  · exact h

@[reducible] protected def isEuclidean [L.HasAxiomFive]
    (hP : ∀ X : Proofset L, X.IsNonproofset → ∀ Ω,
      Xᶜ ∉ P Ω → Ω ∈ (relativeBasicCanonicity L P).toModel.box
        ((relativeBasicCanonicity L P).toModel.dia X)) :
    (relativeBasicCanonicity L P).toModel.IsEuclidean := by
  apply Canonicity.isEuclidean
  intro X hX Ω hΩ
  apply hP X hX
  rcases relativeBasicCanonicity.iff_mem_dia.mp hΩ with ⟨hΩ₁, (h | hΩ₂)⟩
  · exfalso
    obtain ⟨A, hA⟩ := iff_not_isNonproofset_exists.mp h
    apply hX (∼A)
    grind
  · exact hΩ₂

/-
`relativeBasicCanonicity` does not automatically satisfy the symmetry frame condition: unlike
seriality, reflexivity, transitivity, and euclideanness, closing the dual inclusion
`◇□X ⊆ X` for a non-proofset `X` under the extra neighborhoods `P` requires relating `X` back to
the complement of a proofset, which is not derivable from `hP` alone. This case is left open,
ported from an earlier attempt.

protected instance isSymmetric [L.HasAxiomGeach ⟨1, 0, 1, 0⟩]
    (hP₁ : ∀ X : Proofset L, X.IsNonproofset → ∀ Ω,
      ((relativeBasicCanonicity L P).toModel.box X)ᶜ ∉ P Ω → Ω ∈ X) :
    (relativeBasicCanonicity L P).toModel.IsSymmetric := by
  apply Canonicity.isSymmetric'
  intro X hX Ω hΩ
  apply hP₁ X hX
  rcases relativeBasicCanonicity.iff_mem_dia.mp hΩ with ⟨hΩ, (⟨A, hA⟩ | hΩ)⟩
  · rw [hA] at hΩ
    sorry
  · exact hΩ
-/

end relativeBasicCanonicity

namespace minimalRelativeMaximalCanonicity

protected instance isSerial [L.HasAxiomD] : (minimalRelativeMaximalCanonicity L).toModel.IsSerial :=
  relativeBasicCanonicity.isSerial (by tauto)

protected instance isReflexive [L.HasAxiomT] :
    (minimalRelativeMaximalCanonicity L).toModel.IsReflexive :=
  relativeBasicCanonicity.isReflexive (by tauto)

protected instance isTransitive [L.HasAxiomFour] :
    (minimalRelativeMaximalCanonicity L).toModel.IsTransitive :=
  relativeBasicCanonicity.isTransitive (by tauto)

end minimalRelativeMaximalCanonicity

namespace maximalRelativeMaximalCanonicity

protected instance isEuclidean [L.HasAxiomFive] :
    (maximalRelativeMaximalCanonicity L).toModel.IsEuclidean :=
  relativeBasicCanonicity.isEuclidean (by tauto)

end maximalRelativeMaximalCanonicity

end

end
