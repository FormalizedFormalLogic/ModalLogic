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

abbrev frame_3_10529440 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0, 2}, Set.univ}
    | 1 => {{0}, {0, 1}, {0, 2}, Set.univ}
    | 2 => {{0, 2}, Set.univ}⟩

lemma frame_3_10529440.box_mono {X Y : Set (Fin 3)} (h : X ⊆ Y) :
    frame_3_10529440.box X ⊆ frame_3_10529440.box Y := by
  intro w hw
  fin_cases w <;>
    simp only [Frame.box, frame_3_10529440, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
  · rcases hw with rfl | rfl
    · have h0 : (0 : Fin 3) ∈ Y := h (by simp)
      have h2 : (2 : Fin 3) ∈ Y := h (by simp)
      by_cases h1 : (1 : Fin 3) ∈ Y
      · right; ext i; fin_cases i <;> simp_all
      · left; ext i; fin_cases i <;> simp_all
    · right; ext i
      have : i ∈ Set.univ := trivial
      have := h this
      fin_cases i <;> simp_all
  · rcases hw with rfl | rfl | rfl | rfl
    · have h0 : (0 : Fin 3) ∈ Y := h (by simp)
      by_cases h1 : (1 : Fin 3) ∈ Y <;> by_cases h2 : (2 : Fin 3) ∈ Y
      · right; right; right; ext i; fin_cases i <;> simp_all
      · right; left; ext i; fin_cases i <;> simp_all
      · right; right; left; ext i; fin_cases i <;> simp_all
      · left; ext i; fin_cases i <;> simp_all
    · have h0 : (0 : Fin 3) ∈ Y := h (by simp)
      have h1 : (1 : Fin 3) ∈ Y := h (by simp)
      by_cases h2 : (2 : Fin 3) ∈ Y
      · right; right; right; ext i; fin_cases i <;> simp_all
      · right; left; ext i; fin_cases i <;> simp_all
    · have h0 : (0 : Fin 3) ∈ Y := h (by simp)
      have h2 : (2 : Fin 3) ∈ Y := h (by simp)
      by_cases h1 : (1 : Fin 3) ∈ Y
      · right; right; right; ext i; fin_cases i <;> simp_all
      · right; right; left; ext i; fin_cases i <;> simp_all
    · right; right; right; ext i
      have : i ∈ Set.univ := trivial
      have := h this
      fin_cases i <;> simp_all
  · rcases hw with rfl | rfl
    · have h0 : (0 : Fin 3) ∈ Y := h (by simp)
      have h2 : (2 : Fin 3) ∈ Y := h (by simp)
      by_cases h1 : (1 : Fin 3) ∈ Y
      · right; ext i; fin_cases i <;> simp_all
      · left; ext i; fin_cases i <;> simp_all
    · right; ext i
      have : i ∈ Set.univ := trivial
      have := h this
      fin_cases i <;> simp_all

instance : frame_3_10529440.IsMonotonic where
  mono _ _ := Set.subset_inter
    (frame_3_10529440.box_mono Set.inter_subset_left)
    (frame_3_10529440.box_mono Set.inter_subset_right)

instance : frame_3_10529440.IsRegular where
  regular X Y w hw := by
    fin_cases w <;>
      simp only [Frame.box, frame_3_10529440, Set.mem_setOf_eq, Set.mem_inter_iff,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
    · obtain ⟨hX, hY⟩ := hw
      rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
        simp only [Set.ext_iff, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          Set.mem_univ] <;> decide
    · obtain ⟨hX, hY⟩ := hw
      rcases hX with rfl | rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl | rfl <;>
        simp only [Set.ext_iff, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          Set.mem_univ] <;> decide
    · obtain ⟨hX, hY⟩ := hw
      rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
        simp only [Set.ext_iff, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          Set.mem_univ] <;> decide

instance : frame_3_10529440.IsSerial where
  serial X w hw := by
    simp only [Frame.dia, Frame.box, Set.mem_compl_iff, Set.mem_setOf_eq]
    fin_cases w <;>
      simp only [Frame.box, frame_3_10529440, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢
    · rcases hw with rfl | rfl <;>
        simp only [Set.ext_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ,
          Set.mem_compl_iff] <;> decide
    · rcases hw with rfl | rfl | rfl | rfl <;>
        simp only [Set.ext_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ,
          Set.mem_compl_iff] <;> decide
    · rcases hw with rfl | rfl <;>
        simp only [Set.ext_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ,
          Set.mem_compl_iff] <;> decide

lemma frame_3_10529440.box_empty :
    frame_3_10529440.box (∅ : Set (Fin 3)) = ∅ := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_10529440, Set.ext_iff] <;> decide

lemma frame_3_10529440.box_zero :
    frame_3_10529440.box ({0} : Set (Fin 3)) = {1} := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_10529440, Set.ext_iff] <;> decide

lemma frame_3_10529440.box_one :
    frame_3_10529440.box ({1} : Set (Fin 3)) = ∅ := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_10529440, Set.ext_iff] <;> decide

lemma frame_3_10529440.box_two :
    frame_3_10529440.box ({2} : Set (Fin 3)) = ∅ := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_10529440, Set.ext_iff] <;> decide

lemma frame_3_10529440.box_zero_one :
    frame_3_10529440.box ({0, 1} : Set (Fin 3)) = {1} := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_10529440, Set.ext_iff] <;> decide

lemma frame_3_10529440.box_zero_two :
    frame_3_10529440.box ({0, 2} : Set (Fin 3)) = Set.univ := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_10529440]

lemma frame_3_10529440.box_one_two :
    frame_3_10529440.box ({1, 2} : Set (Fin 3)) = ∅ := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_10529440, Set.ext_iff] <;> decide

lemma frame_3_10529440.box_univ :
    frame_3_10529440.box (Set.univ : Set (Fin 3)) = Set.univ := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_10529440]

instance : frame_3_10529440.IsEuclidean := by
  apply Frame.IsEuclidean.of_alt
  intro X a ha
  have hcompl : {b | X ∉ frame_3_10529440.𝒩 b} = (frame_3_10529440.box X)ᶜ := by
    ext b; simp [Frame.box]
  rw [hcompl]
  by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;>
    by_cases h2 : (2 : Fin 3) ∈ X
  · have hXeq : X = Set.univ := by ext i; fin_cases i <;> simp_all
    exact absurd ha (by subst hXeq; fin_cases a <;> simp)
  · have hXeq : X = {0, 1} := by ext i; fin_cases i <;> simp_all
    subst hXeq; rw [frame_3_10529440.box_zero_one]
    fin_cases a <;> simp [frame_3_10529440, Set.ext_iff] <;> decide
  · have hXeq : X = {0, 2} := by ext i; fin_cases i <;> simp_all
    exact absurd ha (by subst hXeq; fin_cases a <;> simp)
  · have hXeq : X = {0} := by ext i; fin_cases i <;> simp_all
    subst hXeq; rw [frame_3_10529440.box_zero]
    fin_cases a <;> simp [frame_3_10529440, Set.ext_iff] <;> decide
  · have hXeq : X = {1, 2} := by ext i; fin_cases i <;> simp_all
    subst hXeq; rw [frame_3_10529440.box_one_two]; fin_cases a <;> simp
  · have hXeq : X = {1} := by ext i; fin_cases i <;> simp_all
    subst hXeq; rw [frame_3_10529440.box_one]; fin_cases a <;> simp
  · have hXeq : X = {2} := by ext i; fin_cases i <;> simp_all
    subst hXeq; rw [frame_3_10529440.box_two]; fin_cases a <;> simp
  · have hXeq : X = ∅ := by ext i; fin_cases i <;> simp_all
    subst hXeq; rw [frame_3_10529440.box_empty]; fin_cases a <;> simp

lemma frame_3_10529440.not_isTransitive :
    ¬frame_3_10529440.IsTransitive := by
  intro hT
  have h := hT.trans ({0} : Set (Fin 3))
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq] at h
  rw [frame_3_10529440.box_zero, frame_3_10529440.box_one] at h
  exact absurd (h (show (1 : Fin 3) ∈ ({1} : Set (Fin 3)) by rfl)) (by simp)

lemma frame_3_10529440.not_valid_axiomFour :
    ¬frame_3_10529440 ⊧ (Axioms.Four #0 : Formula ℕ) :=
  fun h => frame_3_10529440.not_isTransitive (isTransitive_of_valid_axiomFour h)

end
