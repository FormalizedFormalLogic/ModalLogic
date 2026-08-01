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

abbrev frame_3_6 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0}, {1}}
    | 1 => ∅
    | 2 => ∅⟩

lemma frame_3_6.box_singleton_zero :
    frame_3_6.box ({0} : Set (Fin 3)) = {0} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_6, Set.ext_iff]

lemma frame_3_6.box_singleton_one :
    frame_3_6.box ({1} : Set (Fin 3)) = {0} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_6, Set.ext_iff]

instance : frame_3_6.HasPropertyK where
  K X Y := by
    rintro w ⟨hw₁, hw₂⟩
    fin_cases w
    · simp only [Frame.box, frame_3_6, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw₁ hw₂
      exfalso
      have h2 : (2 : Fin 3) ∈ Xᶜ ∪ Y := by
        rcases hw₂ with rfl | rfl <;> simp
      rcases hw₁ with h | h <;> rw [h] at h2 <;> simp at h2
    · simp [Frame.box, frame_3_6] at hw₂
    · simp [Frame.box, frame_3_6] at hw₂

instance : frame_3_6.NotContainsEmpty := ⟨fun x => by
  fin_cases x <;> simp⟩

lemma frame_3_6.dia_singleton_zero :
    frame_3_6.dia ({0} : Set (Fin 3)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.dia, Frame.box, frame_3_6, Set.ext_iff]; decide

lemma frame_3_6.dia_singleton_one :
    frame_3_6.dia ({1} : Set (Fin 3)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.dia, Frame.box, frame_3_6, Set.ext_iff]; decide

instance : frame_3_6.IsSerial where
  serial X := by
    intro w hw
    fin_cases w
    · simp only [Frame.box, frame_3_6, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · rw [frame_3_6.dia_singleton_zero]; trivial
      · rw [frame_3_6.dia_singleton_one]; trivial
    · simp [Frame.box, frame_3_6] at hw
    · simp [Frame.box, frame_3_6] at hw

lemma frame_3_6.not_valid_axiomM [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_6 ⊧ (Axioms.M #a #b : Formula α) := fun h => by
  have h0 := h (fun c => if c = a then Set.univ else if c = b then {0} else ∅) 0
  simp [Forces, Frame.box, frame_3_6, Ne.symm hab] at h0
  rcases h0 with h0 | h0 <;> exact absurd h0 (by simp [Set.ext_iff]; decide)

instance : frame_3_6.IsTransitive where
  trans X := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    intro w hw
    fin_cases w
    · simp only [Frame.box, frame_3_6, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · simp [frame_3_6.box_singleton_zero]
      · simp [frame_3_6.box_singleton_one, frame_3_6.box_singleton_zero]
    · simp [Frame.box, frame_3_6] at hw
    · simp [Frame.box, frame_3_6] at hw

@[simp]
lemma frame_3_6.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_6 ⊧ (Axioms.C #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0} else if c = b then {1} else Set.univ, 0, by
      unfold NotForces Forces; simp [Frame.box, frame_3_6, Set.ext_iff, Ne.symm hab]⟩

end
