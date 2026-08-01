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

abbrev frame_2_90 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {{0}, Set.univ}
    | 1 => {∅, {1}}⟩

lemma frame_2_90.not_containsUnit : ¬frame_2_90.ContainsUnit := by
  intro h
  have h1 : (1 : Fin 2) ∈ frame_2_90.box (Set.univ : Set (Fin 2)) := by
    rw [h.contains_unit]; trivial
  simp [Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff] at h1

lemma frame_2_90.not_valid_axiomN :
    ¬frame_2_90 ⊧ (Axioms.N : Formula α) :=
  fun h => frame_2_90.not_containsUnit (containsUnit_of_valid_axiomN h)

lemma frame_2_90.box_empty : frame_2_90.box (∅ : Set (Fin 2)) = {1} := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]

lemma frame_2_90.box_zero : frame_2_90.box ({0} : Set (Fin 2)) = {0} := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]

lemma frame_2_90.box_one : frame_2_90.box ({1} : Set (Fin 2)) = {1} := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]

lemma frame_2_90.box_univ : frame_2_90.box (Set.univ : Set (Fin 2)) = {0} := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]

instance : frame_2_90.HasPropertyK where
  K X Y w := by
    intro ⟨h1, h2⟩
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
        simp_all [← Set.Fin2.eq_univ, frame_2_90.box_empty, frame_2_90.box_zero,
          frame_2_90.box_one, frame_2_90.box_univ]

lemma frame_2_90.not_valid_axiomM [DecidableEq α] (hab : a ≠ b) :
    ¬frame_2_90 ⊧ (Axioms.M #a #b : Formula α) := fun h => by
  have h0 := h (fun c => if c = a then ∅ else if c = b then {0} else Set.univ) 1
  simp [Forces, Frame.box, Set.ext_iff, frame_2_90, Ne.symm hab] at h0

instance : frame_2_90.IsEuclidean where
  eucl X := by
    have hbox0 : frame_2_90.box ({0} : Set (Fin 2)) = {0} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
    have hbox1 : frame_2_90.box ({1} : Set (Fin 2)) = {1} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl
    · have hdia : frame_2_90.dia ({0, 1} : Set (Fin 2)) = {0} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hbox0]
    · have hdia : frame_2_90.dia ({0} : Set (Fin 2)) = {0} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hbox0]
    · have hdia : frame_2_90.dia ({1} : Set (Fin 2)) = {1} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hbox1]
    · have hdia : frame_2_90.dia (∅ : Set (Fin 2)) = {1} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
      rw [hdia, hbox1]

instance : frame_2_90.IsSerial where
  serial X := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      intro y hy <;> fin_cases y <;>
        simp_all [Frame.box, Frame.dia, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]

instance : frame_2_90.IsTransitive where
  trans X := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    have hboxE : frame_2_90.box (∅ : Set (Fin 2)) = {1} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
    have hbox0 : frame_2_90.box ({0} : Set (Fin 2)) = {0} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
    have hbox1 : frame_2_90.box ({1} : Set (Fin 2)) = {1} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
    have hboxU : frame_2_90.box ({0, 1} : Set (Fin 2)) = {0} := by
      ext y; fin_cases y <;> simp [Frame.box, frame_2_90, Set.Fin2.eq_univ, Set.ext_iff]
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl
    · rw [hboxU, hbox0]
    · rw [hbox0, hbox0]
    · rw [hbox1, hbox1]
    · rw [hboxE, hbox1]

instance : frame_2_90.IsRegular where
  regular X Y w hw := by
    fin_cases w <;>
      simp only [Frame.box, frame_2_90, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢
    · obtain ⟨hX, hY⟩ := hw
      rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp
    · obtain ⟨hX, hY⟩ := hw
      rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp

@[simp]
lemma frame_2_90.not_valid_axiomP : ¬frame_2_90 ⊧ (Axioms.P : Formula α) := fun h => by
  have h1 := (notContainsEmpty_of_valid_axiomP h).not_contains_empty 1
  simp at h1

end
