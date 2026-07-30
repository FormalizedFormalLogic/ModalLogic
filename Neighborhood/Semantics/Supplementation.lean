module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomGeach

/-!
# Supplementation of a neighborhood frame

The *supplementation* of a neighborhood frame `F` upward-closes every neighborhood family: `X`
is a neighborhood of `x` in `F.supplementation` exactly when some subset of `X` is already a
neighborhood of `x` in `F`. It is the smallest monotonic frame refining `F`, and every world
that forces `X` on `F` still forces it on `F.supplementation`.
-/

@[expose] public section

variable {κ : Type u} [Nonempty κ] {F : Frame κ} {X Y : Set κ} {x : κ}

/-- The supplementation of `F`: `X` is a neighborhood of `x` iff some subset of `X` already is a
neighborhood of `x` in `F`. -/
def Frame.supplementation (F : Frame κ) : Frame κ where
  𝒩 x X := ∃ Y ⊆ X, x ∈ F.box Y

namespace Frame.supplementation

@[simp, grind =]
lemma iff_exists_subset : x ∈ F.supplementation.box X ↔ ∃ Y ⊆ X, x ∈ F.box Y := Iff.rfl

lemma mem_box_of_mem_original_box (hx : x ∈ F.box X) : x ∈ F.supplementation.box X :=
  iff_exists_subset.mpr ⟨X, le_refl X, hx⟩

lemma box_aux : F.supplementation.box X = ⋃₀ {Z | ∃ Y ⊆ X, F.box Y = Z} := by
  ext w
  simp only [iff_exists_subset, Set.mem_sUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨Y, hY₁, hY₂⟩; exact ⟨F.box Y, ⟨Y, hY₁, rfl⟩, hY₂⟩
  · rintro ⟨_, ⟨Y, hY₁, rfl⟩, hY₂⟩; exact ⟨Y, hY₁, hY₂⟩

lemma subset (X : Set κ) : F.box X ⊆ F.supplementation.box X := fun _ hx =>
  mem_box_of_mem_original_box hx

lemma monotonic (h : X ⊆ Y) : F.supplementation.box X ⊆ F.supplementation.box Y := by
  intro x hx
  obtain ⟨X', hX', hX⟩ := iff_exists_subset.mp hx
  exact iff_exists_subset.mpr ⟨X', hX'.trans h, hX⟩

lemma monotonic_iterated (h : X ⊆ Y) (n) :
    F.supplementation.box^[n] X ⊆ F.supplementation.box^[n] Y := by
  induction n with
  | zero => simpa
  | succ n ih =>
    rw [Function.iterate_succ']
    exact monotonic ih

lemma itl_reduce : F.supplementation.supplementation.box X = F.supplementation.box X := by
  ext x
  constructor
  · rintro ⟨Y, hYX, Z, hZY, hZ⟩
    exact iff_exists_subset.mpr ⟨Z, hZY.trans hYX, hZ⟩
  · intro hx
    exact subset X hx

instance isMonotonic : F.supplementation.IsMonotonic := by
  constructor
  intro X Y x hx
  obtain ⟨W, hW₁, hW₂⟩ := iff_exists_subset.mp hx
  exact ⟨iff_exists_subset.mpr ⟨W, hW₁.trans Set.inter_subset_left, hW₂⟩,
    iff_exists_subset.mpr ⟨W, hW₁.trans Set.inter_subset_right, hW₂⟩⟩

instance isReflexive [F.IsReflexive] : F.supplementation.IsReflexive := by
  constructor
  intro X x hx
  obtain ⟨Y, hY₁, hY₂⟩ := iff_exists_subset.mp hx
  exact hY₁ (F.refl hY₂)

instance containsUnit [F.ContainsUnit] : F.supplementation.ContainsUnit := by
  constructor
  ext x
  apply iff_of_true _ (Set.mem_univ x)
  exact iff_exists_subset.mpr ⟨Set.univ, le_refl _, F.univ_mem x⟩

instance isTransitive [F.IsTransitive] : F.supplementation.IsTransitive := by
  constructor
  intro X x hx
  obtain ⟨Y, hYX, hY⟩ := iff_exists_subset.mp hx
  exact monotonic_iterated hYX 2 (monotonic (subset Y) (subset (F.box Y) (F.trans hY)))

instance isRegular [F.IsRegular] : F.supplementation.IsRegular := by
  constructor
  intro X Y x hx
  obtain ⟨hX, hY⟩ := hx
  obtain ⟨X', hX'₁, hX'₂⟩ := iff_exists_subset.mp hX
  obtain ⟨Y', hY'₁, hY'₂⟩ := iff_exists_subset.mp hY
  exact iff_exists_subset.mpr ⟨X' ∩ Y', Set.inter_subset_inter hX'₁ hY'₁, F.regular ⟨hX'₂, hY'₂⟩⟩

end Frame.supplementation

section

variable {α : Type u} {L : Logic α}

/-- The supplementation of `basicCanonicity L`, augmented with the monotonicity axiom `M` so
that boxed formulas of `L` correspond exactly to the neighborhoods of the supplemented canonical
model. -/
abbrev supplementedBasicCanonicity (L : Logic α) [DecidableEq α] [L.Cl] [L.HasRE] [L.HasAxiomM]
    [Nonempty (MaximalConsistentSet L)] : Canonicity L where
  𝒩 := (basicCanonicity L).toModel.supplementation.𝒩
  def_𝒩 := by
    intro Ω A
    constructor
    · intro h
      exact ⟨proofset L A, Set.Subset.rfl, A, h, rfl⟩
    · rintro ⟨Y, hY₁, B, hB, rfl⟩
      exact proofset.box_subset_of_subset hY₁ hB
  V a := proofset L #a
  def_V _ := rfl

variable [DecidableEq α] [L.Cl] [L.HasRE] [L.HasAxiomM] [Nonempty (MaximalConsistentSet L)]

instance : (supplementedBasicCanonicity L).toModel.IsMonotonic :=
  Frame.supplementation.isMonotonic (F := (basicCanonicity L).toModel.toFrame)

instance [L.HasAxiomC] : (supplementedBasicCanonicity L).toModel.IsRegular :=
  Frame.supplementation.isRegular (F := (basicCanonicity L).toModel.toFrame)

instance [L.HasAxiomN] : (supplementedBasicCanonicity L).toModel.ContainsUnit :=
  Frame.supplementation.containsUnit (F := (basicCanonicity L).toModel.toFrame)

instance [L.HasAxiomT] : (supplementedBasicCanonicity L).toModel.IsReflexive :=
  Frame.supplementation.isReflexive (F := (basicCanonicity L).toModel.toFrame)

instance [L.HasAxiomFour] : (supplementedBasicCanonicity L).toModel.IsTransitive :=
  Frame.supplementation.isTransitive (F := (basicCanonicity L).toModel.toFrame)

/-- The supplementation of `relativeBasicCanonicity L P`, augmented with the monotonicity axiom
`M` and a compatibility condition `hP` ensuring that every extra neighborhood `Y` witnessing a
non-proofset `X` at `Ω` (with `Y ⊆ X`) forces `□A ∈ Ω` whenever `Y ⊆ proofset L A`. -/
def supplementedRelativeCanonicity (L : Logic α)
    [L.Cl] [L.HasRE] [L.HasAxiomM] [Nonempty (MaximalConsistentSet L)]
    (P : MaximalConsistentSet L → Set (Proofset L))
    (hP : ∀ Y : Proofset L, Y.IsNonproofset → ∀ Ω, Y ∈ P Ω → ∀ A, Y ⊆ proofset L A → □A ∈ Ω) :
    Canonicity L where
  𝒩 := (relativeBasicCanonicity L P).toModel.supplementation.𝒩
  def_𝒩 := by
    intro Ω A
    constructor
    · intro h
      exact ⟨proofset L A, Set.Subset.rfl, Or.inl ⟨A, h, rfl⟩⟩
    · rintro ⟨Y, hY₁, (⟨B, hB, rfl⟩ | ⟨hYnp, hY₂⟩)⟩
      · exact proofset.box_subset_of_subset hY₁ hB
      · exact hP Y hYnp Ω hY₂ A hY₁
  V a := proofset L #a
  def_V _ := rfl

end

end
