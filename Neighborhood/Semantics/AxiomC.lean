module

public import Neighborhood.Axioms
public import Neighborhood.Semantics.Basic
public import Neighborhood.Semantics.Completeness
public import Mathlib.Data.Fintype.Basic

/-!
# Axiom `C` on neighborhood frames

The regularity condition on neighborhood frames and its correspondence with the axiom
`C := (□A ⋏ □B) 🡒 □(A ⋏ B)`: a frame is regular exactly when the neighborhoods of a world are
closed under (finite) intersection, which is exactly the requirement that `C` be valid on the
frame.
-/

@[expose] public section

variable {κ : Type u} [Nonempty κ] {α : Type v} {F : Frame κ}

/-- A frame is regular when its neighborhoods are closed under intersection: if `X` and `Y` are
both neighborhoods of a world, so is `X ∩ Y`. -/
class Frame.IsRegular (F : Frame κ) : Prop where
  regular : ∀ X Y : Set κ, F.box X ∩ F.box Y ⊆ F.box (X ∩ Y)

lemma Frame.regular [F.IsRegular] {X Y : Set κ} : F.box X ∩ F.box Y ⊆ F.box (X ∩ Y) :=
  Frame.IsRegular.regular X Y

open Classical in
lemma Frame.regular_finset_iUnion [F.IsRegular] {ι : Type*} (s : Finset ι) (f : ι → Set κ)
    (hs : s.Nonempty) : (⋂ i ∈ s, F.box (f i)) ⊆ F.box (⋂ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp_all
  | insert i s hi ih =>
    wlog hs : s.Nonempty
    · simp_all
    replace ih := ih hs
    apply Set.Subset.trans ?_ (show f i ∩ ⋂ j ∈ s, f j = ⋂ j ∈ insert i s, f j by
      simp ▸ F.regular (X := f i) (Y := ⋂ j ∈ s, f j))
    suffices (F.box (f i)) ∩ (⋂ j ∈ s, F.box (f j)) ⊆ F.box (⋂ j ∈ s, f j) by simpa
    grind

open Classical in
lemma Frame.regular_finite_iUnion [F.IsRegular] {ι : Type*} [Fintype ι] [Nonempty ι] {X : ι → Set κ} :
    (⋂ i : ι, F.box (X i)) ⊆ F.box (⋂ i : ι, X i) := by
  simpa using Frame.regular_finset_iUnion (F := F) Finset.univ X (by simp)

instance : Frame.simple_blackhole.IsRegular := ⟨by
  intro X Y e ⟨hX, hY⟩
  simp_all [Frame.box]⟩

@[simp, grind]
theorem valid_axiomC_of_isRegular [F.IsRegular] {A B : Formula α} : F ⊧ Axioms.C A B := by
  intro V x
  rw [forces_imp]
  intro h
  rw [forces_and] at h
  rw [forces_box, Model.truthset.eq_and]
  exact F.regular ⟨forces_box.mp h.1, forces_box.mp h.2⟩

theorem isRegular_of_valid_axiomC (h : ∀ A B : Formula ℕ, F ⊧ Axioms.C A B) : F.IsRegular := by
  constructor
  rintro X Y x ⟨hX, hY⟩
  have h₂ := h (.atom 0) (.atom 1) (fun a => match a with | 0 => X | 1 => Y | _ => ∅) x
  rw [forces_imp] at h₂
  rw [forces_and] at h₂
  rw [forces_box, forces_box, forces_box, Model.truthset.eq_and] at h₂
  exact h₂ ⟨hX, hY⟩

section

variable {α : Type u} {L : Logic α} [DecidableEq α] [L.Cl] [L.HasRE] [L.Consistent]

instance [L.HasAxiomC] : (basicCanonicity L).toModel.IsRegular := by
  constructor
  rintro X Y Ω ⟨hX, hY⟩
  obtain ⟨A, rfl, hA⟩ := basicCanonicity.iff_mem_box_exists_fml.mp hX
  obtain ⟨B, rfl, hB⟩ := basicCanonicity.iff_mem_box_exists_fml.mp hY
  rw [← proofset.eq_and, Canonicity.box_proofset]
  exact MaximalConsistentSet.mdp_provable Logic.axiomC (MaximalConsistentSet.iff_mem_and.mpr ⟨hA, hB⟩)

end

end
