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

abbrev frame_3_43176 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0, 1}, {0, 2}, Set.univ}
    | 1 => {{0, 1}, {0, 2}, Set.univ}
    | 2 => ∅⟩

lemma frame_3_43176.box_zero_one :
    frame_3_43176.box ({0, 1} : Set (Fin 3)) = {0, 1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_43176, Set.ext_iff]

lemma frame_3_43176.box_zero_two :
    frame_3_43176.box ({0, 2} : Set (Fin 3)) = {0, 1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_43176, Set.ext_iff]

lemma frame_3_43176.box_univ :
    frame_3_43176.box (Set.univ : Set (Fin 3)) = {0, 1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_43176]

instance : frame_3_43176.IsSerial := ⟨fun X w hw => by
  simp only [Frame.box, frame_3_43176, Set.mem_setOf_eq] at hw
  simp only [Frame.dia, Frame.box, frame_3_43176, Set.mem_compl_iff, Set.mem_setOf_eq]
  fin_cases w <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
  · rcases hw with rfl | rfl | rfl <;>
      rintro (h | h | h) <;> (have h0 := Set.ext_iff.mp h 0; simp at h0)
  · rcases hw with rfl | rfl | rfl <;>
      rintro (h | h | h) <;> (have h0 := Set.ext_iff.mp h 0; simp at h0)
  · exact hw.elim⟩

instance : frame_3_43176.IsTransitive := ⟨fun X w hw => by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
  simp only [Frame.box, frame_3_43176, Set.mem_setOf_eq] at hw
  fin_cases w <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false] at hw
  · rcases hw with rfl | rfl | rfl
    · rw [frame_3_43176.box_zero_one]; simp [Frame.box, frame_3_43176]
    · rw [frame_3_43176.box_zero_two]; simp [Frame.box, frame_3_43176]
    · rw [frame_3_43176.box_univ]; simp [Frame.box, frame_3_43176]
  · rcases hw with rfl | rfl | rfl
    · rw [frame_3_43176.box_zero_one]; simp [Frame.box, frame_3_43176]
    · rw [frame_3_43176.box_zero_two]; simp [Frame.box, frame_3_43176]
    · rw [frame_3_43176.box_univ]; simp [Frame.box, frame_3_43176]⟩

lemma frame_3_43176.not_isRegular :
    ¬frame_3_43176.IsRegular := by
  intro hR
  have h := hR.regular ({0, 1} : Set (Fin 3)) ({0, 2} : Set (Fin 3))
  have h0 : (0 : Fin 3) ∈ frame_3_43176.box {0, 1} ∩ frame_3_43176.box {0, 2} := by
    rw [frame_3_43176.box_zero_one, frame_3_43176.box_zero_two]; simp
  have hmem := h h0
  have heq : ({0, 1} : Set (Fin 3)) ∩ {0, 2} = {0} := by ext i; fin_cases i <;> simp
  rw [heq] at hmem
  simp only [Frame.box, frame_3_43176, Set.mem_setOf_eq] at hmem
  have h1 : (1 : Fin 3) ∉ ({0} : Set (Fin 3)) := by simp
  have h2 : (2 : Fin 3) ∉ ({0} : Set (Fin 3)) := by simp
  rcases hmem with h | h | h
  · exact h1 (h ▸ (by simp))
  · exact h2 (h ▸ (by simp))
  · exact h1 (h ▸ (by simp))

lemma frame_3_43176.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_43176 ⊧ (Axioms.C #a #b : Formula α) := by
  intro hv
  apply frame_3_43176.not_isRegular
  constructor
  rintro X Y x ⟨hX, hY⟩
  have h₂ := hv (fun c => if c = a then X else if c = b then Y else ∅) x
  rw [forces_imp, forces_and, forces_box, forces_box, forces_box, Model.truthset.eq_and] at h₂
  simp only [Model.truthset.eq_atom, if_neg (Ne.symm hab)] at h₂
  exact h₂ ⟨hX, hY⟩

end
