module

public import Neighborhood.Semantics.Basic
public import Neighborhood.Logic.MaximalConsistentSet
public import Neighborhood.Logic.Calculus

/-!
# Canonical neighborhood models

The canonical model construction for the classical non-normal modal logics: the *proofset* of a
formula is the set of maximal consistent sets containing it, and a *canonicity* datum assigns
neighborhoods to maximal consistent sets so that `□A` belongs to `Ω` exactly when the proofset of
`A` is one of `Ω`'s neighborhoods. Every canonicity datum yields a canonical model on which
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

/-- A canonical neighborhood datum for `L`: an assignment of neighborhoods to the maximal
consistent sets of `L` under which `□A` belongs to `Ω` exactly when the proofset of `A` is one of
`Ω`'s neighborhoods, together with a valuation reproducing the proofsets of the atoms. -/
structure Canonicity (L : Logic α) where
  𝒩 : MaximalConsistentSet L → Set (Set (MaximalConsistentSet L))
  def_𝒩 : ∀ Ω : MaximalConsistentSet L, ∀ A, □A ∈ Ω ↔ proofset L A ∈ 𝒩 Ω
  V : α → Set (MaximalConsistentSet L)
  def_V : ∀ a, V a = proofset L (.atom a)

namespace Canonicity

attribute [simp] def_𝒩 def_V

variable [DecidableEq α] [L.Cl] [Nonempty (MaximalConsistentSet L)] {𝓒 : Canonicity L}

/-- The canonical model of `𝓒`. -/
def toModel (𝓒 : Canonicity L) : Model (MaximalConsistentSet L) α where
  𝒩 := 𝓒.𝒩
  Val := 𝓒.V

omit [DecidableEq α] [L.Cl] in
@[simp]
lemma box_proofset : 𝓒.toModel.box (proofset L A) = proofset L (□A) := by
  ext Ω; exact (𝓒.def_𝒩 Ω A).symm

omit [DecidableEq α] [L.Cl] in
@[simp]
lemma boxItr_proofset {n : ℕ} : 𝓒.toModel.box^[n] (proofset L A) = proofset L (□^[n]A) := by
  induction n generalizing A with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ, Function.comp_apply, box_proofset, ih]

@[simp]
lemma dia_proofset : 𝓒.toModel.dia (proofset L A) = proofset L (◇A) := by
  rw [proofset.eq_neg, ← box_proofset (𝓒 := 𝓒), proofset.eq_neg]
  rfl

@[simp]
lemma diaItr_proofset {n : ℕ} : 𝓒.toModel.dia^[n] (proofset L A) = proofset L (◇^[n]A) := by
  induction n generalizing A with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ, Function.comp_apply, dia_proofset, ih]

omit [DecidableEq α] [L.Cl] in
lemma iff_box {Ω : MaximalConsistentSet L} : □A ∈ Ω ↔ Ω ∈ 𝓒.toModel.box (proofset L A) :=
  𝓒.def_𝒩 Ω A

lemma iff_dia {Ω : MaximalConsistentSet L} : ◇A ∈ Ω ↔ Ω ∈ 𝓒.toModel.dia (proofset L A) := by
  have h : ◇A ∈ Ω ↔ □(∼A) ∉ Ω := MaximalConsistentSet.iff_mem_neg (A := □(∼A))
  rw [h, iff_box (𝓒 := 𝓒), proofset.eq_neg]
  rfl

/-- The truth lemma: the proofset of `A` is exactly the truth set of `A` in `𝓒`'s canonical
model. -/
lemma truthlemma : proofset L A = 𝓒.toModel.truthset A := by
  induction A with
  | hfalsum => simp
  | hatom a => exact (𝓒.def_V a).symm
  | himp A B ihA ihB => simp [ihA, ihB]
  | hbox A ihA => rw [Model.truthset.eq_box, ← ihA, box_proofset]

/-- Every formula valid on `𝓒`'s canonical model is a theorem of `L`: the generic completeness
producer for a canonicity datum. -/
theorem mem_of_valid (𝓒 : Canonicity L) (h : 𝓒.toModel ⊧ A) : A ∈ L := by
  by_contra hA
  obtain ⟨Ω, hΩ⟩ :=
    MaximalConsistentSet.lindenbaum (FormulaSet.unprovable_iff_singleton_neg_consistent.mpr hA)
  have hΩA : ∼A ∈ Ω := hΩ rfl
  have hAΩ : Ω ∈ proofset L A := by rw [𝓒.truthlemma]; exact h Ω
  exact (MaximalConsistentSet.iff_mem_neg.mp hΩA) hAΩ

end Canonicity

/-- The canonicity datum whose neighborhoods at `Ω` are exactly the proofsets already witnessed
by a boxed formula of `Ω`. -/
def basicCanonicity (L : Logic α) [DecidableEq α] [L.Cl] [L.HasRE] : Canonicity L where
  𝒩 Ω (X : Proofset L) := ∃ A, □A ∈ Ω ∧ X = proofset L A
  def_𝒩 := by
    intro Ω A
    constructor
    · intro h; exact ⟨A, h, rfl⟩
    · rintro ⟨B, hB, hAB⟩
      exact (proofset.iff_mem_of_eq (proofset.eq_boxed_of_eq hAB)).mpr hB
  V a := proofset L (.atom a)
  def_V _ := rfl

namespace basicCanonicity

variable [DecidableEq α] [L.Cl] [L.HasRE] [Nonempty (MaximalConsistentSet L)] {X : Proofset L}
  {Ω : MaximalConsistentSet L}

lemma iff_mem_box_exists_fml :
    Ω ∈ (basicCanonicity L).toModel.box X ↔ ∃ A, X = proofset L A ∧ Ω ∈ proofset L (□A) := by
  constructor
  · rintro ⟨A, hA, rfl⟩; exact ⟨A, rfl, hA⟩
  · rintro ⟨A, rfl, hA⟩; exact ⟨A, hA, rfl⟩

@[grind →]
lemma not_isNonproofset_of_mem_box (h : Ω ∈ (basicCanonicity L).toModel.box X) :
    ¬X.IsNonproofset := by
  obtain ⟨A, rfl, _⟩ := iff_mem_box_exists_fml.mp h
  simp

lemma iff_mem_dia_forall_fml :
    Ω ∈ (basicCanonicity L).toModel.dia X ↔ ∀ A, Xᶜ ≠ proofset L A ∨ Ω ∉ proofset L (□A) := by
  show Ω ∉ (basicCanonicity L).toModel.box Xᶜ ↔ _
  simp only [iff_mem_box_exists_fml, not_exists, not_and_or]

end basicCanonicity

/-- `basicCanonicity` together with an extra family `P` of neighborhoods for the non-proofsets
of each maximal consistent set. -/
def relativeBasicCanonicity (L : Logic α) [DecidableEq α] [L.Cl] [L.HasRE]
    (P : MaximalConsistentSet L → Set (Proofset L)) : Canonicity L where
  𝒩 Ω (X : Proofset L) := (∃ A, □A ∈ Ω ∧ X = proofset L A) ∨ (X.IsNonproofset ∧ X ∈ P Ω)
  def_𝒩 := by
    intro Ω A
    constructor
    · intro h; exact Or.inl ⟨A, h, rfl⟩
    · rintro (⟨B, hB, hAB⟩ | h)
      · exact (proofset.iff_mem_of_eq (proofset.eq_boxed_of_eq hAB)).mpr hB
      · exact absurd rfl (h.1 A)
  V a := proofset L (.atom a)
  def_V _ := rfl

namespace relativeBasicCanonicity

variable [DecidableEq α] [L.Cl] [L.HasRE] [Nonempty (MaximalConsistentSet L)]
  {P : MaximalConsistentSet L → Set (Proofset L)} {X : Proofset L} {Ω : MaximalConsistentSet L}

protected lemma iff_mem_box :
    Ω ∈ (relativeBasicCanonicity L P).toModel.box X ↔
      Ω ∈ (basicCanonicity L).toModel.box X ∨ (X.IsNonproofset ∧ X ∈ P Ω) := Iff.rfl

protected lemma iff_mem_dia :
    Ω ∈ (relativeBasicCanonicity L P).toModel.dia X ↔
      Ω ∉ (basicCanonicity L).toModel.box Xᶜ ∧ (¬Xᶜ.IsNonproofset ∨ Xᶜ ∉ P Ω) := by
  show ¬Ω ∈ (relativeBasicCanonicity L P).toModel.box Xᶜ ↔ _
  rw [relativeBasicCanonicity.iff_mem_box, not_or, not_and_or]

end relativeBasicCanonicity

/-- `relativeBasicCanonicity` with no extra neighborhoods on the non-proofsets. -/
abbrev minimalRelativeMaximalCanonicity (L : Logic α) [DecidableEq α] [L.Cl] [L.HasRE] :
    Canonicity L :=
  relativeBasicCanonicity L (fun _ _ => False)

lemma minimalRelativeMaximalCanonicity.iff_minimal [DecidableEq α] [L.Cl] [L.HasRE] [Nonempty (MaximalConsistentSet L)]
    {X : Proofset L} {Ω : MaximalConsistentSet L} :
    Ω ∈ (minimalRelativeMaximalCanonicity L).toModel.box X ↔
      Ω ∈ (basicCanonicity L).toModel.box X := by
  rw [relativeBasicCanonicity.iff_mem_box]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact h
    · exact h.elim
  · exact Or.inl

/-- `relativeBasicCanonicity` with every non-proofset as an extra neighborhood. -/
abbrev maximalRelativeMaximalCanonicity (L : Logic α) [DecidableEq α] [L.Cl] [L.HasRE] :
    Canonicity L :=
  relativeBasicCanonicity L (fun _ _ => True)

end
