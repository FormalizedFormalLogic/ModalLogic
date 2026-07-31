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

abbrev frame_3_168 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0, 1}, {0, 2}, Set.univ}
    | 1 => ∅
    | 2 => ∅⟩

/-- A set of worlds containing `0` and `1` is either `{0, 1}` or the whole frame. -/
lemma frame_3_168.eq_of_mem01 {X : Set (Fin 3)} (h0 : (0 : Fin 3) ∈ X) (h1 : (1 : Fin 3) ∈ X) :
    X = {0, 1} ∨ X = Set.univ := by
  by_cases h2 : (2 : Fin 3) ∈ X
  · right; ext i; fin_cases i <;> simp_all
  · left; ext i; fin_cases i <;> simp_all

/-- A set of worlds containing `0` and `2` is either `{0, 2}` or the whole frame. -/
lemma frame_3_168.eq_of_mem02 {X : Set (Fin 3)} (h0 : (0 : Fin 3) ∈ X) (h2 : (2 : Fin 3) ∈ X) :
    X = {0, 2} ∨ X = Set.univ := by
  by_cases h1 : (1 : Fin 3) ∈ X
  · right; ext i; fin_cases i <;> simp_all
  · left; ext i; fin_cases i <;> simp_all

lemma frame_3_168.mem_nbhd_zero_of_mem01 {X : Set (Fin 3)} (h0 : (0 : Fin 3) ∈ X)
    (h1 : (1 : Fin 3) ∈ X) : X ∈ frame_3_168.𝒩 0 := by
  rcases frame_3_168.eq_of_mem01 h0 h1 with rfl | rfl <;> simp

lemma frame_3_168.mem_nbhd_zero_of_mem02 {X : Set (Fin 3)} (h0 : (0 : Fin 3) ∈ X)
    (h2 : (2 : Fin 3) ∈ X) : X ∈ frame_3_168.𝒩 0 := by
  rcases frame_3_168.eq_of_mem02 h0 h2 with rfl | rfl <;> simp

instance : frame_3_168.IsMonotonic := ⟨fun X Y w hw => by
  simp only [Frame.box, frame_3_168, Set.mem_setOf_eq] at hw
  fin_cases w
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    simp only [Frame.box, Set.mem_inter_iff, Set.mem_setOf_eq]
    rcases hw with h | h | h
    · have h0 : (0 : Fin 3) ∈ X ∩ Y := by rw [h]; simp
      have h1 : (1 : Fin 3) ∈ X ∩ Y := by rw [h]; simp
      exact ⟨frame_3_168.mem_nbhd_zero_of_mem01 h0.1 h1.1,
        frame_3_168.mem_nbhd_zero_of_mem01 h0.2 h1.2⟩
    · have h0 : (0 : Fin 3) ∈ X ∩ Y := by rw [h]; simp
      have h2 : (2 : Fin 3) ∈ X ∩ Y := by rw [h]; simp
      exact ⟨frame_3_168.mem_nbhd_zero_of_mem02 h0.1 h2.1,
        frame_3_168.mem_nbhd_zero_of_mem02 h0.2 h2.2⟩
    · have h0 : (0 : Fin 3) ∈ X ∩ Y := by rw [h]; trivial
      have h1 : (1 : Fin 3) ∈ X ∩ Y := by rw [h]; trivial
      exact ⟨frame_3_168.mem_nbhd_zero_of_mem01 h0.1 h1.1,
        frame_3_168.mem_nbhd_zero_of_mem01 h0.2 h1.2⟩
  · simp at hw
  · simp at hw⟩

instance : frame_3_168.IsReflexive := ⟨fun X w hw => by
  fin_cases w <;>
    simp only [Frame.box, frame_3_168, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
  · rcases hw with rfl | rfl | rfl <;> simp
  · exact hw.elim
  · exact hw.elim⟩

lemma frame_3_168.not_isRegular :
    ¬frame_3_168.IsRegular := by
  intro hR
  have h := hR.regular ({0, 1} : Set (Fin 3)) ({0, 2} : Set (Fin 3))
  have h0 : (0 : Fin 3) ∈ frame_3_168.box {0, 1} ∩ frame_3_168.box {0, 2} := by
    constructor <;> simp [Frame.box, frame_3_168]
  have hmem := h h0
  have heq : ({0, 1} : Set (Fin 3)) ∩ {0, 2} = {0} := by ext i; fin_cases i <;> simp
  rw [heq] at hmem
  simp only [Frame.box, frame_3_168, Set.mem_setOf_eq] at hmem
  have h1 : (1 : Fin 3) ∉ ({0} : Set (Fin 3)) := by simp
  have h2 : (2 : Fin 3) ∉ ({0} : Set (Fin 3)) := by simp
  rcases hmem with h | h | h
  · exact h1 (h ▸ (by simp))
  · exact h2 (h ▸ (by simp))
  · exact h1 (h ▸ (by simp))

lemma frame_3_168.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_168 ⊧ (Axioms.C #a #b : Formula α) := by
  intro hv
  apply frame_3_168.not_isRegular
  constructor
  rintro X Y x ⟨hX, hY⟩
  have h₂ := hv (fun c => if c = a then X else if c = b then Y else ∅) x
  rw [forces_imp, forces_and, forces_box, forces_box, forces_box, Model.truthset.eq_and] at h₂
  simp only [Model.truthset.eq_atom, if_neg (Ne.symm hab)] at h₂
  exact h₂ ⟨hX, hY⟩

end
