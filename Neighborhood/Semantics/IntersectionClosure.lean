module

public import Neighborhood.Semantics.Supplementation
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Lemmas
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Data.Fintype.Sets

/-!
# Intersection closure and quasi-filtration of a neighborhood frame

Two closure operations on neighborhood frames used to build regular (`M`+`C`) canonical and
finite countermodels:

* `Frame.intersectionClosure` closes the neighborhood function under finite nonempty
  intersections. This always yields a regular frame, without ever removing a neighborhood the
  original frame already had.
* `Frame.quasiFiltering`, the supplementation of the intersection closure, additionally makes
  the frame monotonic, while still preserving the reflexivity, transitivity and unit-containment
  of the original frame.
-/

@[expose] public section

variable {κ : Type u} [Nonempty κ] {F : Frame κ}

/-- The intersection closure of a frame: a set `X` is a neighborhood of `a` in
`F.intersectionClosure` exactly when `X` is a finite nonempty intersection of neighborhoods of
`a` in `F`. -/
def Frame.intersectionClosure (F : Frame κ) : Frame κ where
  𝒩 a X := ∃ Xs : Finset (Set κ), Xs ≠ ∅ ∧ X = ⋂ Xi ∈ Xs, Xi ∧ ∀ Xi ∈ Xs, Xi ∈ F.𝒩 a

instance Frame.intersectionClosure.isRegular : F.intersectionClosure.IsRegular := by
  constructor
  intro X Y a
  rw [Set.mem_inter_iff]
  simp only [intersectionClosure, Frame.box, ne_eq, and_imp]
  rintro ⟨Xs, hXs₁, rfl, hX₂⟩ ⟨Ys, hYs₁, rfl, hY₂⟩
  refine ⟨Xs ∪ Ys, ?_, ?_, ?_⟩
  · simp only [Finset.union_eq_empty]
    grind
  · ext b
    show b ∈ ((⋂ Xi ∈ Xs, Xi) ∩ (⋂ Xi ∈ Ys, Xi) : Set κ) ↔ b ∈ ⋂ Xi ∈ Xs ∪ Ys, Xi
    simp only [Set.mem_inter_iff, Set.mem_iInter₂, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩ i (hi | hi)
      · exact h1 i hi
      · exact h2 i hi
    · intro h
      exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · simp only [Finset.mem_union]
    rintro Z (hZ | hZ)
    · apply hX₂; assumption
    · apply hY₂; assumption

/-- Every neighborhood of the original frame remains a neighborhood of its intersection
closure. -/
lemma Frame.intersectionClosure.mem_box_of_mem_original_box {x : κ} {s : Set κ} :
    x ∈ F.box s → x ∈ F.intersectionClosure.box s := by
  intro hx
  use {s}
  refine ⟨?_, ?_, ?_⟩ <;> simp_all [Frame.box]

/-- The quasi-filtration of a frame: the supplementation of its intersection closure. -/
def Frame.quasiFiltering (F : Frame κ) : Frame κ := F.intersectionClosure.supplementation

namespace Frame.quasiFiltering

open Classical in
lemma symm_𝒩 : F.quasiFiltering.𝒩 = F.supplementation.intersectionClosure.𝒩 := by
  dsimp [quasiFiltering]
  ext w X
  constructor
  · rintro ⟨_, hYs₃, ⟨Ys, hYs₁, rfl, hYs₂⟩⟩
    let Y := ⋂ Yi ∈ Ys, Yi
    have : X = ⋂ Yi ∈ Ys, Yi ∪ (X \ Y) := calc
      _ = Y ∪ (X \ Y) := by
        ext x
        constructor
        · tauto
        · rintro (h | ⟨h, _⟩)
          · apply hYs₃ h
          · assumption
      _ = _ := by
        ext x
        simp [Y]
        grind
    rw [this]
    use Ys.image (λ Yi => Yi ∪ (X \ Y))
    refine ⟨?_, ?_, ?_⟩
    · simpa
    · simp
    · simp only [Frame.supplementation]
      intro Xi hXi
      obtain ⟨Yi, hYi, rfl⟩ := Finset.mem_image.mp hXi
      use Yi
      constructor
      · exact Set.subset_union_left
      · apply hYs₂
        assumption
  · rintro ⟨Ys, hYs₁, rfl, hYs₂⟩
    let Zs := Finset.image (α := Ys) (λ ⟨Yi, hYi⟩ => hYs₂ Yi hYi |>.choose) Finset.univ
    use (⋂ Zi ∈ Zs, Zi)
    constructor
    · rintro a ha _ ⟨Y, _, rfl⟩
      suffices Y ∈ Ys → a ∈ Y by simpa
      rintro hY
      apply hYs₂ Y hY |>.choose_spec |>.1
      simp only [← Finset.attach_eq_univ, Finset.mem_image, Finset.mem_attach,
        true_and, Subtype.exists, Set.iInter_exists, Set.mem_iInter, Zs] at ha
      apply ha
      · rfl
      · assumption
    · use Zs
      refine ⟨?_, ?_, ?_⟩
      · simpa [Zs]
      · rfl
      · simp [Zs]
        rintro _ Yi hYi rfl
        apply hYs₂ Yi hYi |>.choose_spec |>.2

lemma symm_box : F.quasiFiltering.box = F.supplementation.intersectionClosure.box := by
  ext X x
  simp [Frame.box, symm_𝒩]

instance isMonotonic : F.quasiFiltering.IsMonotonic := Frame.supplementation.isMonotonic

instance isRegular : F.quasiFiltering.IsRegular := Frame.supplementation.isRegular

instance isTransitive [F.IsTransitive] : F.quasiFiltering.IsTransitive := by
  constructor
  intro X w hw
  obtain ⟨Y, hY₁, Ys, hYs₁, rfl, hYs₂⟩ := Frame.supplementation.iff_exists_subset.mp hw
  apply Frame.mono' (F := F.quasiFiltering) (X := (⋂ Yi ∈ Ys, F.box Yi)) $ by
    intro a ha
    use (⋂ Yi ∈ Ys, Yi)
    refine ⟨?_, Ys, ?_, ?_, ?_⟩
    · assumption
    · assumption
    · tauto
    · intro Xi hXi
      exact Set.mem_iInter₂.mp ha Xi hXi
  replace hYs₂ : w ∈ ⋂ Yi ∈ Ys, F.box^[2] Yi :=
    Set.mem_iInter₂.mpr (fun Yi hYi => F.trans (hYs₂ Yi hYi))
  use (⋂ Yi ∈ Ys, F.box Yi)
  constructor
  · rfl
  · use Ys.image F.box
    refine ⟨?_, ?_, ?_⟩
    · simpa
    · symm
      exact Finset.set_biInter_finset_image
    · simp [Frame.box] at hYs₂ ⊢
      exact hYs₂

instance containsUnit [F.ContainsUnit] : F.quasiFiltering.ContainsUnit := by
  constructor
  ext x
  apply iff_of_true _ (Set.mem_univ x)
  show ∃ Y ⊆ (Set.univ : Set κ), x ∈ F.intersectionClosure.box Y
  use Set.univ
  refine ⟨le_refl _, ?_⟩
  use {Set.univ}
  simp

/-- Every neighborhood of the original frame remains a neighborhood of its quasi-filtration. -/
lemma mem_box_of_mem_original_box {x : κ} {s : Set κ} :
    x ∈ F.box s → x ∈ F.quasiFiltering.box s := by
  intro hx
  suffices h : x ∈ F.supplementation.intersectionClosure.box s by rw [symm_box]; exact h
  apply Frame.intersectionClosure.mem_box_of_mem_original_box
  apply Frame.supplementation.mem_box_of_mem_original_box
  exact hx

end Frame.quasiFiltering
end
