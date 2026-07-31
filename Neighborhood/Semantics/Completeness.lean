module

public import Neighborhood.Semantics.Basic
public import Neighborhood.Logic.MaximalConsistentSet
public import Neighborhood.Logic.Calculus

/-!
# Canonical neighborhood models

The canonical model construction for the classical non-normal modal logics: the *proofset* of a
formula is the set of maximal consistent sets containing it, and a *CanonicalModel* datum assigns
neighborhoods to maximal consistent sets so that `□A` belongs to `Ω` exactly when the proofset of
`A` is one of `Ω`'s neighborhoods. Every CanonicalModel datum yields a canonical model on which
membership of a formula in a maximal consistent set agrees with its truth (the truth lemma), from
which completeness follows by Lindenbaum's lemma.
-/

@[expose] public section

variable {α : Type u} {L : Logic α} {A B : Formula α}

/-- Sets of maximal consistent sets of `L`, i.e. candidate proofsets. -/
abbrev Proofset (L : Logic α) := Set (MaximalConsistentSet L)

/-- The proofset of `A`: the maximal consistent sets of `L` containing `A`. -/
def proofset (L : Logic α) (A : Formula α) : Proofset L := { Ω | A ∈ Ω }

/-- A set of maximal consistent sets that is not the proofset of any formula. -/
def Proofset.IsNonproofset (P : Proofset L) : Prop := ∀ A, P ≠ proofset L A

lemma iff_not_isNonproofset_exists {P : Proofset L} :
    ¬P.IsNonproofset ↔ ∃ A, P = proofset L A := by
  simp [Proofset.IsNonproofset]

@[simp]
lemma not_isNonproofset_proofset : ¬(proofset L A).IsNonproofset := fun h => h A rfl

namespace proofset

variable {Ω : MaximalConsistentSet L}

@[grind =] lemma iff_mem : A ∈ Ω ↔ Ω ∈ proofset L A := Iff.rfl

lemma mem_of_mem_of_subset (h : proofset L A ⊆ proofset L B) (hA : A ∈ Ω) : B ∈ Ω :=
  iff_mem.mpr (h (iff_mem.mp hA))

lemma iff_mem_of_eq (h : proofset L A = proofset L B) : A ∈ Ω ↔ B ∈ Ω := by
  rw [iff_mem, iff_mem, h]

variable [DecidableEq α] [L.Cl]

@[simp, grind =] lemma eq_top : proofset L (⊤ : Formula α) = Set.univ := by
  ext Ω; simp [proofset]

omit [DecidableEq α] in
@[simp, grind =] lemma eq_bot : proofset L (⊥ : Formula α) = ∅ := by
  ext Ω; simp [proofset]

@[simp, grind =] lemma eq_neg : proofset L (∼A) = (proofset L A)ᶜ := by
  ext Ω; simp [proofset]

@[simp, grind =] lemma eq_imp : proofset L (A 🡒 B) = (proofset L A)ᶜ ∪ proofset L B := by
  ext Ω; simp [proofset]; tauto

@[simp, grind =] lemma eq_and : proofset L (A ⋏ B) = proofset L A ∩ proofset L B := by
  ext Ω; simp [proofset]

@[simp, grind =] lemma eq_or : proofset L (A ⋎ B) = proofset L A ∪ proofset L B := by
  ext Ω; simp [proofset]; tauto

/-- A formula of `L` is exactly one whose proofset is everything. -/
lemma iff_provable_eq_univ : A ∈ L ↔ proofset L A = Set.univ := by
  rw [← MaximalConsistentSet.iff_forall_mem_provable, Set.eq_univ_iff_forall]
  simp [proofset]

@[grind =]
lemma imp_subset : A 🡒 B ∈ L ↔ proofset L A ⊆ proofset L B := by
  rw [← MaximalConsistentSet.iff_forall_mem_provable]
  constructor
  · intro h Ω hΩ
    exact iff_mem.mp (MaximalConsistentSet.iff_mem_imp.mp (h Ω) (iff_mem.mpr hΩ))
  · intro h Ω
    exact MaximalConsistentSet.iff_mem_imp.mpr fun hA => iff_mem.mpr (h (iff_mem.mp hA))

@[grind =]
lemma iff_subset : A 🡘 B ∈ L ↔ proofset L A = proofset L B := by
  rw [Formula.iff_eq, Logic.K_intro_iff, imp_subset, imp_subset]
  exact Set.Subset.antisymm_iff.symm

lemma eq_boxed_of_eq [L.HasRE] (h : proofset L A = proofset L B) :
    proofset L (□A) = proofset L (□B) :=
  iff_subset.mp (Logic.re (iff_subset.mpr h))

@[grind →]
lemma box_subset_of_subset [L.HasRE] [L.HasAxiomM] (h : proofset L A ⊆ proofset L B) :
    proofset L (□A) ⊆ proofset L (□B) :=
  imp_subset.mp (Logic.rm (imp_subset.mpr h))

end proofset

section

variable [DecidableEq α] [L.Cl] {X : Proofset L}

/-- The complement of a non-proofset is itself a non-proofset. -/
lemma Proofset.IsNonproofset.compl (hX : X.IsNonproofset) : Xᶜ.IsNonproofset := by
  intro A hA
  exact hX (∼A) (by rw [← compl_compl X, hA, proofset.eq_neg])

end

structure CanonicalModel (L : Logic α) [Nonempty (MaximalConsistentSet L)] extends Model (MaximalConsistentSet L) α where
  def_𝒩 : ∀ Ω A, □A ∈ Ω ↔ proofset L A ∈ toModel.𝒩 Ω
  def_V : ∀ a, toModel.Val a = proofset L #a

namespace CanonicalModel

attribute [simp] def_𝒩 def_V

variable [DecidableEq α] [L.Cl] [Nonempty (MaximalConsistentSet L)] {C : CanonicalModel L}

omit [DecidableEq α] [L.Cl] in
@[simp]
lemma box_proofset : C.box (proofset L A) = proofset L (□A) := by
  ext Ω; exact (C.def_𝒩 Ω A).symm

omit [DecidableEq α] [L.Cl] in
@[simp]
lemma boxItr_proofset {n : ℕ} : C.box^[n] (proofset L A) = proofset L (□^[n]A) := by
  induction n generalizing A with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ, Function.comp_apply, box_proofset, ih]

@[simp]
lemma dia_proofset : C.dia (proofset L A) = proofset L (◇A) := by
  rw [proofset.eq_neg, ← box_proofset (C := C), proofset.eq_neg]
  rfl

@[simp]
lemma diaItr_proofset {n : ℕ} : C.dia^[n] (proofset L A) = proofset L (◇^[n]A) := by
  induction n generalizing A with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ, Function.comp_apply, dia_proofset, ih]

omit [DecidableEq α] [L.Cl] in
lemma iff_box {Ω : MaximalConsistentSet L} : □A ∈ Ω ↔ Ω ∈ C.box (proofset L A) :=
  C.def_𝒩 Ω A

lemma iff_dia {Ω : MaximalConsistentSet L} : ◇A ∈ Ω ↔ Ω ∈ C.dia (proofset L A) := by
  have h : ◇A ∈ Ω ↔ □(∼A) ∉ Ω := MaximalConsistentSet.iff_mem_neg (A := □(∼A))
  rw [h, iff_box (C := C), proofset.eq_neg]
  rfl

/-- The truth lemma: the proofset of `A` is exactly the truth set of `A` in `C`'s canonical
model. -/
lemma truthlemma : proofset L A = C.truthset A := by
  induction A with
  | hfalsum => simp
  | hatom a => exact (C.def_V a).symm
  | himp A B ihA ihB => simp [ihA, ihB]
  | hbox A ihA => rw [Model.truthset.eq_box, ← ihA, box_proofset]

/-- Every formula valid on `C`'s canonical model is a theorem of `L`: the generic completeness
producer for a CanonicalModel datum. -/
theorem mem_of_valid (C : CanonicalModel L) (h : C.toModel ⊧ A) : A ∈ L := by
  by_contra hA
  obtain ⟨Ω, hΩ⟩ :=
    MaximalConsistentSet.lindenbaum (FormulaSet.unprovable_iff_singleton_neg_consistent.mpr hA)
  have hΩA : ∼A ∈ Ω := hΩ rfl
  have hAΩ : Ω ∈ proofset L A := by rw [C.truthlemma]; exact h Ω
  exact (MaximalConsistentSet.iff_mem_neg.mp hΩA) hAΩ

end CanonicalModel

/-- The CanonicalModel datum whose neighborhoods at `Ω` are exactly the proofsets already witnessed
by a boxed formula of `Ω`. -/
def basicCanonicalModel (L : Logic α) [DecidableEq α] [L.Cl] [L.HasRE] [Nonempty (MaximalConsistentSet L)] : CanonicalModel L where
  𝒩 Ω (X : Proofset L) := ∃ A, □A ∈ Ω ∧ X = proofset L A
  def_𝒩 := by
    intro Ω A
    constructor
    · intro h; exact ⟨A, h, rfl⟩
    · rintro ⟨B, hB, hAB⟩
      exact (proofset.iff_mem_of_eq (proofset.eq_boxed_of_eq hAB)).mpr hB
  Val a := proofset L #a
  def_V _ := rfl

namespace basicCanonicalModel

variable [DecidableEq α] [L.Cl] [L.HasRE] [Nonempty (MaximalConsistentSet L)] {X : Proofset L}
  {Ω : MaximalConsistentSet L}

lemma iff_mem_box_exists_fml : Ω ∈ (basicCanonicalModel L).box X ↔ ∃ A, X = proofset L A ∧ Ω ∈ proofset L (□A) := by
  constructor
  · rintro ⟨A, hA, rfl⟩; exact ⟨A, rfl, hA⟩
  · rintro ⟨A, rfl, hA⟩; exact ⟨A, hA, rfl⟩

@[grind →]
lemma not_isNonproofset_of_mem_box (h : Ω ∈ (basicCanonicalModel L).box X) :
    ¬X.IsNonproofset := by
  obtain ⟨A, rfl, _⟩ := iff_mem_box_exists_fml.mp h
  simp

lemma iff_mem_dia_forall_fml :
    Ω ∈ (basicCanonicalModel L).dia X ↔ ∀ A, Xᶜ ≠ proofset L A ∨ Ω ∉ proofset L (□A) := by
  show Ω ∉ (basicCanonicalModel L).box Xᶜ ↔ _
  simp only [iff_mem_box_exists_fml, not_exists, not_and_or]

end basicCanonicalModel

/-- `basicCanonicalModel` together with an extra family `P` of neighborhoods for the non-proofsets
of each maximal consistent set. -/
def relativeBasicCanonicalModel (L : Logic α) [DecidableEq α] [L.Cl] [L.HasRE] [Nonempty (MaximalConsistentSet L)]
  (P : MaximalConsistentSet L → Set (Proofset L)) : CanonicalModel L where
  𝒩 Ω (X : Proofset L) := (∃ A, □A ∈ Ω ∧ X = proofset L A) ∨ (X.IsNonproofset ∧ X ∈ P Ω)
  def_𝒩 := by
    intro Ω A
    constructor
    · intro h; exact Or.inl ⟨A, h, rfl⟩
    · rintro (⟨B, hB, hAB⟩ | h)
      · exact (proofset.iff_mem_of_eq (proofset.eq_boxed_of_eq hAB)).mpr hB
      · exact absurd rfl (h.1 A)
  Val a := proofset L #a
  def_V _ := rfl

variable
  [DecidableEq α] [L.Cl] [L.HasRE] [Nonempty (MaximalConsistentSet L)]
  {P : MaximalConsistentSet L → Set (Proofset L)}
  {Ω : MaximalConsistentSet L}
  {X : Proofset L}

namespace relativeBasicCanonicalModel

protected lemma iff_mem_box :
  Ω ∈ (relativeBasicCanonicalModel L P).box X ↔
  Ω ∈ (basicCanonicalModel L).box X ∨ (X.IsNonproofset ∧ X ∈ P Ω) := Iff.rfl

protected lemma iff_mem_dia :
  Ω ∈ (relativeBasicCanonicalModel L P).dia X ↔
  Ω ∉ (basicCanonicalModel L).box Xᶜ ∧ (¬Xᶜ.IsNonproofset ∨ Xᶜ ∉ P Ω) := by
  show ¬Ω ∈ (relativeBasicCanonicalModel L P).box Xᶜ ↔ _
  rw [relativeBasicCanonicalModel.iff_mem_box, not_or, not_and_or]

/-- On a non-proofset, membership in a neighborhood of `(relativeBasicCanonicalModel L P)`
reduces to membership in `P Ω`: the alternative of being a boxed proofset is impossible. -/
protected lemma iff_mem_box_of_isNonproofset (hX : X.IsNonproofset) :
  Ω ∈ (relativeBasicCanonicalModel L P).box X ↔ X ∈ P Ω := by
  rw [relativeBasicCanonicalModel.iff_mem_box]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact absurd hX (basicCanonicalModel.not_isNonproofset_of_mem_box h)
    · exact h
  · exact fun h => Or.inr ⟨hX, h⟩

end relativeBasicCanonicalModel

/-- `relativeBasicCanonicalModel` with no extra neighborhoods on the non-proofsets. -/
abbrev minimalRelativeMaximalCanonicalModel (L : Logic α) [L.Cl] [L.HasRE] [Nonempty (MaximalConsistentSet L)] :
  CanonicalModel L :=
  relativeBasicCanonicalModel L (fun _ _ => False)

lemma minimalRelativeMaximalCanonicalModel.iff_minimal :
  Ω ∈ (minimalRelativeMaximalCanonicalModel L).box X ↔ Ω ∈ (basicCanonicalModel L).box X := by
  rw [relativeBasicCanonicalModel.iff_mem_box]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact h
    · exact h.elim
  · exact Or.inl

/-- `relativeBasicCanonicalModel` with every non-proofset as an extra neighborhood. -/
abbrev maximalRelativeMaximalCanonicalModel (L : Logic α) [L.Cl] [L.HasRE] [Nonempty (MaximalConsistentSet L)] :
  CanonicalModel L :=
  relativeBasicCanonicalModel L (fun _ _ => True)

/-- `relativeBasicCanonicalModel` with the non-proofsets containing `Ω` as `Ω`'s extra neighborhoods,
`P Ω X := Ω ∈ X`. Pointwise this sits between `minimalRelativeMaximalCanonicalModel` (`P := False`)
and `maximalRelativeMaximalCanonicalModel` (`P := True`), and it is exactly this intermediate choice
that makes the canonical model symmetric.

- [Che80, Theorem 9.8] -/
abbrev intermediateRelativeMaximalCanonicalModel (L : Logic α) [L.Cl] [L.HasRE] [Nonempty (MaximalConsistentSet L)] :
  CanonicalModel L :=
  relativeBasicCanonicalModel L (fun Ω X => Ω ∈ X)

namespace intermediateRelativeMaximalCanonicalModel

lemma box_eq_of_isNonproofset (hX : X.IsNonproofset) : (intermediateRelativeMaximalCanonicalModel L).box X = X := by
  ext Ω
  exact relativeBasicCanonicalModel.iff_mem_box_of_isNonproofset hX

lemma dia_eq_of_isNonproofset (hX : X.IsNonproofset) : (intermediateRelativeMaximalCanonicalModel L).dia X = X := by
  show ((intermediateRelativeMaximalCanonicalModel L).box Xᶜ)ᶜ = X
  rw [box_eq_of_isNonproofset hX.compl, compl_compl]

end intermediateRelativeMaximalCanonicalModel

end
