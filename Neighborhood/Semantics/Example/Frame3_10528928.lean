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
variable {a b : α}

abbrev frame_3_10528928 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0, 2}, Set.univ}
    | 1 => {{0, 1}, {0, 2}, Set.univ}
    | 2 => {{0, 2}, Set.univ}⟩

lemma frame_3_10528928.box_mono {X Y : Set (Fin 3)} (h : X ⊆ Y) :
    frame_3_10528928.box X ⊆ frame_3_10528928.box Y := by
  intro w hw
  fin_cases w
  · simp only [Frame.box, frame_3_10528928, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
    rcases hw with rfl | rfl
    · have h0 : (0 : Fin 3) ∈ Y := h (by simp)
      have h2 : (2 : Fin 3) ∈ Y := h (by simp)
      by_cases h1 : (1 : Fin 3) ∈ Y
      · right; ext i; fin_cases i <;> simp_all
      · left; ext i; fin_cases i <;> simp_all
    · right; ext i
      have : i ∈ (Set.univ : Set (Fin 3)) := trivial
      have := h this
      fin_cases i <;> simp_all
  · simp only [Frame.box, frame_3_10528928, Set.mem_setOf_eq, Set.mem_insert_iff,
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
  · simp only [Frame.box, frame_3_10528928, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
    rcases hw with rfl | rfl
    · have h0 : (0 : Fin 3) ∈ Y := h (by simp)
      have h2 : (2 : Fin 3) ∈ Y := h (by simp)
      by_cases h1 : (1 : Fin 3) ∈ Y
      · right; ext i; fin_cases i <;> simp_all
      · left; ext i; fin_cases i <;> simp_all
    · right; ext i
      have : i ∈ (Set.univ : Set (Fin 3)) := trivial
      have := h this
      fin_cases i <;> simp_all

instance : frame_3_10528928.IsMonotonic where
  mono _ _ := Set.subset_inter
    (frame_3_10528928.box_mono Set.inter_subset_left)
    (frame_3_10528928.box_mono Set.inter_subset_right)

lemma frame_3_10528928.box_zero_one :
    frame_3_10528928.box ({0, 1} : Set (Fin 3)) = {1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_10528928, Set.ext_iff] <;> decide

lemma frame_3_10528928.box_zero_two :
    frame_3_10528928.box ({0, 2} : Set (Fin 3)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_10528928]

lemma frame_3_10528928.box_univ :
    frame_3_10528928.box (Set.univ : Set (Fin 3)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_10528928]

lemma frame_3_10528928.box_singleton_one :
    frame_3_10528928.box ({1} : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_10528928, Set.ext_iff] <;> decide

lemma frame_3_10528928.box_singleton_two :
    frame_3_10528928.box ({2} : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_10528928, Set.ext_iff] <;> decide

lemma frame_3_10528928.box_empty :
    frame_3_10528928.box (∅ : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_10528928, Set.ext_iff] <;> decide

lemma frame_3_10528928.dia_zero_one :
    frame_3_10528928.dia ({0, 1} : Set (Fin 3)) = Set.univ := by
  have hc : ({0, 1} : Set (Fin 3))ᶜ = {2} := by ext i; fin_cases i <;> simp
  simp [Frame.dia, hc, frame_3_10528928.box_singleton_two]

lemma frame_3_10528928.dia_zero_two :
    frame_3_10528928.dia ({0, 2} : Set (Fin 3)) = Set.univ := by
  have hc : ({0, 2} : Set (Fin 3))ᶜ = {1} := by ext i; fin_cases i <;> simp
  simp [Frame.dia, hc, frame_3_10528928.box_singleton_one]

lemma frame_3_10528928.dia_univ :
    frame_3_10528928.dia (Set.univ : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_10528928.box_empty]

instance : frame_3_10528928.IsEuclidean :=
  Frame.IsEuclidean.of_alt (fun X a ha => by
    fin_cases a <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ha
    · obtain ⟨ha1, ha2⟩ := ha
      by_cases hX : X = ({0, 1} : Set (Fin 3))
      · subst hX
        have : {b : Fin 3 | ({0, 1} : Set (Fin 3)) ∉ frame_3_10528928.𝒩 b} = {0, 2} := by
          ext b; fin_cases b <;> simp [ha1, ha2]
        rw [this]; simp
      · have : {b : Fin 3 | X ∉ frame_3_10528928.𝒩 b} = Set.univ := by
          ext b; fin_cases b <;> simp [hX, ha1, ha2]
        rw [this]; simp
    · obtain ⟨ha0, ha1, ha2⟩ := ha
      have : {b : Fin 3 | X ∉ frame_3_10528928.𝒩 b} = Set.univ := by
        ext b; fin_cases b <;> simp [ha0, ha1, ha2]
      rw [this]; simp
    · obtain ⟨ha1, ha2⟩ := ha
      by_cases hX : X = ({0, 1} : Set (Fin 3))
      · subst hX
        have : {b : Fin 3 | ({0, 1} : Set (Fin 3)) ∉ frame_3_10528928.𝒩 b} = {0, 2} := by
          ext b; fin_cases b <;> simp [ha1, ha2]
        rw [this]; simp
      · have : {b : Fin 3 | X ∉ frame_3_10528928.𝒩 b} = Set.univ := by
          ext b; fin_cases b <;> simp [hX, ha1, ha2]
        rw [this]; simp)

instance : frame_3_10528928.IsSerial where
  serial X w hw := by
    have hw' : X ∈ frame_3_10528928.𝒩 w := hw
    fin_cases w <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
    · rcases hw' with rfl | rfl
      · simp [frame_3_10528928.dia_zero_two]
      · simp [frame_3_10528928.dia_univ]
    · rcases hw' with rfl | rfl | rfl
      · simp [frame_3_10528928.dia_zero_one]
      · simp [frame_3_10528928.dia_zero_two]
      · simp [frame_3_10528928.dia_univ]
    · rcases hw' with rfl | rfl
      · simp [frame_3_10528928.dia_zero_two]
      · simp [frame_3_10528928.dia_univ]

lemma frame_3_10528928.not_isRegular :
    ¬frame_3_10528928.IsRegular := fun hR => by
  have h1 : (1 : Fin 3) ∈ frame_3_10528928.box (({0, 1} : Set (Fin 3)) ∩ {0, 2}) :=
    hR.regular ({0, 1} : Set (Fin 3)) ({0, 2} : Set (Fin 3))
      ⟨show ({0, 1} : Set (Fin 3)) ∈ frame_3_10528928.𝒩 1 by simp,
       show ({0, 2} : Set (Fin 3)) ∈ frame_3_10528928.𝒩 1 by simp⟩
  have heq : ({0, 1} : Set (Fin 3)) ∩ {0, 2} = ({0} : Set (Fin 3)) := by
    ext i; fin_cases i <;> simp
  rw [heq] at h1
  change ({0} : Set (Fin 3)) ∈ frame_3_10528928.𝒩 1 at h1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  rcases h1 with h1 | h1 | h1
  · exact absurd ((Set.ext_iff.mp h1 1).mpr (by simp)) (by simp)
  · exact absurd ((Set.ext_iff.mp h1 2).mpr (by simp)) (by simp)
  · exact absurd ((Set.ext_iff.mp h1 1).mpr (by simp)) (by simp)

@[simp]
lemma frame_3_10528928.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_10528928 ⊧ (Axioms.C #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0, 1} else if c = b then {0, 2} else Set.univ, 1, by
      unfold NotForces Forces
      simp [Frame.box, frame_3_10528928, Set.ext_iff, Ne.symm hab]
      decide⟩

lemma frame_3_10528928.not_isTransitive : ¬frame_3_10528928.IsTransitive := fun hT => by
  have h := hT.trans ({0, 1} : Set (Fin 3))
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq] at h
  rw [frame_3_10528928.box_zero_one, frame_3_10528928.box_singleton_one] at h
  exact absurd (h (show (1 : Fin 3) ∈ ({1} : Set (Fin 3)) by simp)) (by simp)

lemma frame_3_10528928.not_valid_axiomFour :
    ¬frame_3_10528928 ⊧ (Axioms.Four #a : Formula α) :=
  fun h => frame_3_10528928.not_isTransitive (isTransitive_of_valid_axiomFour h)

end
