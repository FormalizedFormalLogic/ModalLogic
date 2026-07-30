module

public import Neighborhood.Semantics.AxiomM

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

end Frame.supplementation

end
