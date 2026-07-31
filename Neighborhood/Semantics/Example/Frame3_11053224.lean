module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach
import Mathlib.Tactic.FinCases

@[expose] public section

variable {α : Type u}

abbrev frame_3_11053224 : Frame (Fin 3) := ⟨fun _ => {{0, 1}, {0, 2}, Set.univ}⟩

lemma frame_3_11053224.box_of_not_mem {X : Set (Fin 3)} (h1 : X ≠ {0, 1}) (h2 : X ≠ {0, 2})
    (hu : X ≠ Set.univ) :
    frame_3_11053224.box X = ∅ := by
  ext w
  simp only [Frame.box, frame_3_11053224, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  tauto

lemma frame_3_11053224.box_zero_one :
    frame_3_11053224.box ({0, 1} : Set (Fin 3)) = Set.univ := by
  ext w; simp [Frame.box, frame_3_11053224]

lemma frame_3_11053224.box_zero_two :
    frame_3_11053224.box ({0, 2} : Set (Fin 3)) = Set.univ := by
  ext w; simp [Frame.box, frame_3_11053224]

lemma frame_3_11053224.box_univ :
    frame_3_11053224.box (Set.univ : Set (Fin 3)) = Set.univ := by
  ext w; simp [Frame.box, frame_3_11053224]

lemma frame_3_11053224.box_singleton_one :
    frame_3_11053224.box ({1} : Set (Fin 3)) = ∅ := by
  ext w; simp [Frame.box, frame_3_11053224, Set.ext_iff]; decide

lemma frame_3_11053224.box_singleton_two :
    frame_3_11053224.box ({2} : Set (Fin 3)) = ∅ := by
  ext w; simp [Frame.box, frame_3_11053224, Set.ext_iff]; decide

lemma frame_3_11053224.box_empty :
    frame_3_11053224.box (∅ : Set (Fin 3)) = ∅ := by
  ext w; simp [Frame.box, frame_3_11053224, Set.ext_iff]; decide

lemma frame_3_11053224.box_mono {X Y : Set (Fin 3)} (h : X ⊆ Y) :
    frame_3_11053224.box X ⊆ frame_3_11053224.box Y := by
  intro w hw
  simp only [Frame.box, frame_3_11053224, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hw ⊢
  rcases hw with rfl | rfl | rfl
  · have h0 : (0 : Fin 3) ∈ Y := h (by simp)
    have h1 : (1 : Fin 3) ∈ Y := h (by simp)
    by_cases h2 : (2 : Fin 3) ∈ Y
    · right; right; ext i; fin_cases i <;> simp_all
    · left; ext i; fin_cases i <;> simp_all
  · have h0 : (0 : Fin 3) ∈ Y := h (by simp)
    have h2 : (2 : Fin 3) ∈ Y := h (by simp)
    by_cases h1 : (1 : Fin 3) ∈ Y
    · right; right; ext i; fin_cases i <;> simp_all
    · right; left; ext i; fin_cases i <;> simp_all
  · right; right; ext i
    have : i ∈ (Set.univ : Set (Fin 3)) := trivial
    have := h this
    fin_cases i <;> simp_all

instance : frame_3_11053224.IsMonotonic where
  mono _ _ := Set.subset_inter
    (frame_3_11053224.box_mono Set.inter_subset_left)
    (frame_3_11053224.box_mono Set.inter_subset_right)

lemma frame_3_11053224.box_eq_univ_or_empty (X : Set (Fin 3)) :
    frame_3_11053224.box X = Set.univ ∨ frame_3_11053224.box X = ∅ := by
  by_cases h1 : X = ({0, 1} : Set (Fin 3))
  · exact Or.inl (h1 ▸ frame_3_11053224.box_zero_one)
  by_cases h2 : X = ({0, 2} : Set (Fin 3))
  · exact Or.inl (h2 ▸ frame_3_11053224.box_zero_two)
  by_cases hu : X = Set.univ
  · exact Or.inl (hu ▸ frame_3_11053224.box_univ)
  · exact Or.inr (frame_3_11053224.box_of_not_mem h1 h2 hu)

instance : frame_3_11053224.IsTransitive where
  trans X := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    rcases frame_3_11053224.box_eq_univ_or_empty X with h | h <;> rw [h] <;>
      simp [frame_3_11053224.box_univ]

instance : frame_3_11053224.IsSerial where
  serial X w hw := by
    simp only [Frame.box, frame_3_11053224, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · have hc : ({0, 1} : Set (Fin 3))ᶜ = {2} := by ext i; fin_cases i <;> simp
      simp [Frame.dia, hc, frame_3_11053224.box_singleton_two]
    · have hc : ({0, 2} : Set (Fin 3))ᶜ = {1} := by ext i; fin_cases i <;> simp
      simp [Frame.dia, hc, frame_3_11053224.box_singleton_one]
    · simp [Frame.dia, frame_3_11053224.box_empty]

instance : frame_3_11053224.IsEuclidean :=
  Frame.IsEuclidean.of_alt (fun X a ha => by
    have h : {b : Fin 3 | X ∉ frame_3_11053224.𝒩 b} = Set.univ := by
      ext b; simpa using ha
    rw [h]; simp)

@[simp]
lemma frame_3_11053224.not_valid_axiomC :
    ¬frame_3_11053224 ⊧ (Axioms.C #0 #1 : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0, 1} | 1 => {0, 2} | _ => Set.univ, 0, by
      unfold NotForces Forces
      simp [Frame.box, frame_3_11053224, Set.ext_iff]
      decide⟩

end
