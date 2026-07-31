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
variable {a : α}

abbrev frame_3_8437920 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0, 2}, Set.univ}
    | 1 => {{1, 2}, Set.univ}
    | 2 => {Set.univ}⟩

lemma frame_3_8437920.box_mono {X Y : Set (Fin 3)} (h : X ⊆ Y) :
    frame_3_8437920.box X ⊆ frame_3_8437920.box Y := by
  intro w hw
  fin_cases w <;>
    simp only [Frame.box, frame_3_8437920, Set.mem_setOf_eq, Set.mem_insert_iff,
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
  · rcases hw with rfl | rfl
    · have h1 : (1 : Fin 3) ∈ Y := h (by simp)
      have h2 : (2 : Fin 3) ∈ Y := h (by simp)
      by_cases h0 : (0 : Fin 3) ∈ Y
      · right; ext i; fin_cases i <;> simp_all
      · left; ext i; fin_cases i <;> simp_all
    · right; ext i
      have : i ∈ Set.univ := trivial
      have := h this
      fin_cases i <;> simp_all
  · subst hw
    ext i
    have : i ∈ Set.univ := trivial
    have := h this
    fin_cases i <;> simp_all

instance : frame_3_8437920.IsMonotonic where
  mono _ _ := Set.subset_inter
    (frame_3_8437920.box_mono Set.inter_subset_left)
    (frame_3_8437920.box_mono Set.inter_subset_right)

instance : frame_3_8437920.ContainsUnit := ⟨by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8437920]⟩

instance : frame_3_8437920.IsReflexive where
  refl X w hw := by
    fin_cases w <;>
      simp only [Frame.box, frame_3_8437920, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢ <;>
      rcases hw with rfl | rfl <;> simp

lemma frame_3_8437920.box_0_2 :
    frame_3_8437920.box ({0, 2} : Set (Fin 3)) = {0} := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_8437920, Set.ext_iff] <;> decide

lemma frame_3_8437920.box_1_2 :
    frame_3_8437920.box ({1, 2} : Set (Fin 3)) = {1} := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_8437920, Set.ext_iff] <;> decide

instance : frame_3_8437920.IsSymmetric where
  symm X w hw := by
    fin_cases w
    · by_cases h1 : (1 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X <;>
        simp only [Frame.box, frame_3_8437920, Set.mem_setOf_eq, Set.mem_insert_iff,
          Set.mem_singleton_iff]
      · have hXeq : X = Set.univ := by ext i; fin_cases i <;> simp_all
        subst hXeq
        right; ext x; fin_cases x <;> simp [Frame.dia, Frame.box, Set.ext_iff] <;> decide
      · have hXeq : X = {0, 1} := by ext i; fin_cases i <;> simp_all
        subst hXeq
        right; ext x; fin_cases x <;> simp [Frame.dia, Frame.box, Set.ext_iff] <;> decide
      · have hXeq : X = {0, 2} := by ext i; fin_cases i <;> simp_all
        subst hXeq
        right; ext x; fin_cases x <;> simp [Frame.dia, Frame.box, Set.ext_iff] <;> decide
      · have hXeq : X = {0} := by ext i; fin_cases i <;> simp_all
        subst hXeq
        left; ext x; fin_cases x <;> simp [Frame.dia, Frame.box, Set.ext_iff] <;> decide
    · by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X <;>
        simp only [Frame.box, frame_3_8437920, Set.mem_setOf_eq, Set.mem_insert_iff,
          Set.mem_singleton_iff]
      · have hXeq : X = Set.univ := by ext i; fin_cases i <;> simp_all
        subst hXeq
        right; ext x; fin_cases x <;> simp [Frame.dia, Frame.box, Set.ext_iff] <;> decide
      · have hXeq : X = {0, 1} := by ext i; fin_cases i <;> simp_all
        subst hXeq
        right; ext x; fin_cases x <;> simp [Frame.dia, Frame.box, Set.ext_iff] <;> decide
      · have hXeq : X = {1, 2} := by ext i; fin_cases i <;> simp_all
        subst hXeq
        right; ext x; fin_cases x <;> simp [Frame.dia, Frame.box, Set.ext_iff] <;> decide
      · have hXeq : X = {1} := by ext i; fin_cases i <;> simp_all
        subst hXeq
        left; ext x; fin_cases x <;> simp [Frame.dia, Frame.box, Set.ext_iff] <;> decide
    · by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;>
        simp only [Frame.box, frame_3_8437920, Set.mem_setOf_eq, Set.mem_singleton_iff]
      · have hXeq : X = Set.univ := by ext i; fin_cases i <;> simp_all
        subst hXeq
        ext x; fin_cases x <;> simp [Frame.dia, Frame.box, Set.ext_iff] <;> decide
      · have hXeq : X = {0, 2} := by ext i; fin_cases i <;> simp_all
        subst hXeq
        ext x; fin_cases x <;> simp [Frame.dia, Frame.box, Set.ext_iff] <;> decide
      · have hXeq : X = {1, 2} := by ext i; fin_cases i <;> simp_all
        subst hXeq
        ext x; fin_cases x <;> simp [Frame.dia, Frame.box, Set.ext_iff] <;> decide
      · have hXeq : X = {2} := by ext i; fin_cases i <;> simp_all
        subst hXeq
        ext x; fin_cases x <;> simp [Frame.dia, Frame.box, Set.ext_iff] <;> decide

lemma frame_3_8437920.not_isEuclidean :
    ¬frame_3_8437920.IsEuclidean := fun hE => by
  have hdia : frame_3_8437920.dia ({0} : Set (Fin 3)) = {0, 2} := by
    have hcompl : ({0} : Set (Fin 3))ᶜ = {1, 2} := by ext x; fin_cases x <;> simp
    simp only [Frame.dia, hcompl, frame_3_8437920.box_1_2]
    ext x; fin_cases x <;> simp
  have h2 := hE.eucl {0}
  rw [hdia, frame_3_8437920.box_0_2] at h2
  exact absurd (h2 (show (2 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) by simp)) (by simp)

lemma frame_3_8437920.not_valid_axiomFive :
    ¬frame_3_8437920 ⊧ (Axioms.Five #a : Formula α) :=
  fun h => frame_3_8437920.not_isEuclidean (isEuclidean_of_valid_axiomFive h)

instance : frame_3_8437920.IsRegular where
  regular X Y w hw := by
    fin_cases w <;>
      simp only [Frame.box, frame_3_8437920, Set.mem_inter_iff, Set.mem_setOf_eq,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
    · obtain ⟨hX, hY⟩ := hw
      rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp
    · obtain ⟨hX, hY⟩ := hw
      rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp
    · obtain ⟨hX, hY⟩ := hw
      subst hX; subst hY; simp

lemma frame_3_8437920.not_isTransitive : ¬frame_3_8437920.IsTransitive := by
  intro hT
  have hbox0_2 : frame_3_8437920.box ({0, 2} : Set (Fin 3)) = {0} := frame_3_8437920.box_0_2
  have hbox0_empty : frame_3_8437920.box ({0} : Set (Fin 3)) = ∅ := by
    ext w
    fin_cases w <;> simp [Frame.box, frame_3_8437920, Set.ext_iff] <;> decide
  have hiter : frame_3_8437920.box^[2] ({0, 2} : Set (Fin 3)) = ∅ := by
    show frame_3_8437920.box (frame_3_8437920.box {0, 2}) = ∅
    rw [hbox0_2, hbox0_empty]
  have h1 : (0 : Fin 3) ∈ frame_3_8437920.box ({0, 2} : Set (Fin 3)) := by
    rw [hbox0_2]; rfl
  have h2 := hT.trans ({0, 2} : Set (Fin 3)) h1
  rw [hiter] at h2
  simp at h2

lemma frame_3_8437920.not_valid_axiomFour :
    ¬frame_3_8437920 ⊧ (Axioms.Four #a : Formula α) :=
  fun h => frame_3_8437920.not_isTransitive (isTransitive_of_valid_axiomFour h)

end
