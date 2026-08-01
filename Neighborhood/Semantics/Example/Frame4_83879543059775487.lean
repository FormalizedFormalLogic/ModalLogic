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

abbrev frame_4_83879543059775487 : Frame (Fin 4) :=
  ⟨fun w => match w with
    | 0 => Set.univ
    | 1 => Set.univ
    | 2 => Set.univ
    | 3 => {∅, {0, 1}, {0, 2}, {3}}⟩

lemma frame_4_83879543059775487.mem_box_zero (Y : Set (Fin 4)) :
    (0 : Fin 4) ∈ frame_4_83879543059775487.box Y := by
  simp [Frame.box, frame_4_83879543059775487]

lemma frame_4_83879543059775487.mem_box_one (Y : Set (Fin 4)) :
    (1 : Fin 4) ∈ frame_4_83879543059775487.box Y := by
  simp [Frame.box, frame_4_83879543059775487]

lemma frame_4_83879543059775487.mem_box_two (Y : Set (Fin 4)) :
    (2 : Fin 4) ∈ frame_4_83879543059775487.box Y := by
  simp [Frame.box, frame_4_83879543059775487]

lemma frame_4_83879543059775487.box_eq_univ_or (Y : Set (Fin 4)) :
    frame_4_83879543059775487.box Y = Set.univ ∨
      frame_4_83879543059775487.box Y = {0, 1, 2} := by
  by_cases h3 : (3 : Fin 4) ∈ frame_4_83879543059775487.box Y
  · left
    ext w
    fin_cases w <;>
      simp [frame_4_83879543059775487.mem_box_zero, frame_4_83879543059775487.mem_box_one,
        frame_4_83879543059775487.mem_box_two, h3]
  · right
    ext w
    fin_cases w <;>
      simp [frame_4_83879543059775487.mem_box_zero, frame_4_83879543059775487.mem_box_one,
        frame_4_83879543059775487.mem_box_two, h3]

lemma frame_4_83879543059775487.compl_zero_one_two :
    ({0, 1, 2} : Set (Fin 4))ᶜ = {3} := by
  ext i; fin_cases i <;> simp

lemma frame_4_83879543059775487.box_empty :
    frame_4_83879543059775487.box (∅ : Set (Fin 4)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_83879543059775487]

lemma frame_4_83879543059775487.box_three :
    frame_4_83879543059775487.box ({3} : Set (Fin 4)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_83879543059775487]

lemma frame_4_83879543059775487.dia_eq_empty_or (X : Set (Fin 4)) :
    frame_4_83879543059775487.dia X = ∅ ∨ frame_4_83879543059775487.dia X = {3} := by
  rcases frame_4_83879543059775487.box_eq_univ_or Xᶜ with h | h
  · left; simp [Frame.dia, h]
  · right; simp [Frame.dia, h, frame_4_83879543059775487.compl_zero_one_two]

lemma frame_4_83879543059775487.box_dia_eq_univ (X : Set (Fin 4)) :
    frame_4_83879543059775487.box (frame_4_83879543059775487.dia X) = Set.univ := by
  rcases frame_4_83879543059775487.dia_eq_empty_or X with h | h <;> rw [h]
  · exact frame_4_83879543059775487.box_empty
  · exact frame_4_83879543059775487.box_three

instance : frame_4_83879543059775487.HasPropertyK where
  K X Y := by
    rintro w ⟨hw1, hw2⟩
    fin_cases w
    · exact frame_4_83879543059775487.mem_box_zero Y
    · exact frame_4_83879543059775487.mem_box_one Y
    · exact frame_4_83879543059775487.mem_box_two Y
    · simp only [Frame.box, frame_4_83879543059775487, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw1 hw2
      exfalso
      rcases hw2 with rfl | rfl | rfl | rfl <;>
        rcases hw1 with h | h | h | h <;>
        · have h0 := Set.ext_iff.mp h 0
          have h1 := Set.ext_iff.mp h 1
          have h2 := Set.ext_iff.mp h 2
          have h3 := Set.ext_iff.mp h 3
          clear h
          simp_all

instance : frame_4_83879543059775487.IsSymmetric := ⟨fun X => by
  rw [frame_4_83879543059775487.box_dia_eq_univ]
  exact Set.subset_univ X⟩

instance : frame_4_83879543059775487.IsEuclidean := ⟨fun X => by
  rw [frame_4_83879543059775487.box_dia_eq_univ]
  exact Set.subset_univ _⟩

@[simp]
lemma frame_4_83879543059775487.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_4_83879543059775487 ⊧ (Axioms.C #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0, 1} else if c = b then {0, 2} else Set.univ, 3, by
      unfold NotForces Forces
      simp only [Model.truthset.eq_imp, Model.truthset.eq_bot, Model.truthset.eq_box,
        Model.truthset.eq_atom, Set.mem_compl_iff, Set.mem_union, not_or, not_not, if_true,
        Set.union_empty]
      simp only [Frame.box, frame_4_83879543059775487, Ne.symm hab, if_false, Set.mem_setOf_eq]
      refine ⟨⟨by tauto, by tauto⟩, ?_⟩
      have hcompl : ({0, 1} : Set (Fin 4))ᶜ ∪ ({0, 2} : Set (Fin 4))ᶜ = ({0} : Set (Fin 4))ᶜ := by
        ext i; fin_cases i <;> simp
      rw [hcompl]
      simp only [compl_compl, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
        · have h0 := Set.ext_iff.mp h 0
          have h1 := Set.ext_iff.mp h 1
          have h2 := Set.ext_iff.mp h 2
          have h3 := Set.ext_iff.mp h 3
          simp_all⟩

end
