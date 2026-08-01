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

abbrev frame_3_2359090 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0}, {2}, {0, 2}}
    | 1 => Set.univ
    | 2 => {∅, {0}, {0, 2}}⟩

instance : frame_3_2359090.HasPropertyK where
  K X Y := by
    rintro w ⟨hw₁, hw₂⟩
    fin_cases w
    · simp only [Frame.box, frame_3_2359090, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw₁ hw₂
      exfalso
      have h1 : (1 : Fin 3) ∈ Xᶜ ∪ Y := by
        rcases hw₂ with rfl | rfl | rfl <;> simp
      rcases hw₁ with h | h | h <;> rw [h] at h1 <;> simp at h1
    · simp [Frame.box, frame_3_2359090]
    · simp only [Frame.box, frame_3_2359090, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw₁ hw₂
      exfalso
      have h1 : (1 : Fin 3) ∈ Xᶜ ∪ Y := by
        rcases hw₂ with rfl | rfl | rfl <;> simp
      rcases hw₁ with h | h | h <;> rw [h] at h1 <;> simp at h1

lemma frame_3_2359090.box_empty :
    frame_3_2359090.box (∅ : Set (Fin 3)) = {1, 2} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_2359090, Set.ext_iff]; decide

lemma frame_3_2359090.box_zero :
    frame_3_2359090.box ({0} : Set (Fin 3)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_2359090]

lemma frame_3_2359090.box_one :
    frame_3_2359090.box ({1} : Set (Fin 3)) = {1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_2359090, Set.ext_iff] <;> decide

lemma frame_3_2359090.box_two :
    frame_3_2359090.box ({2} : Set (Fin 3)) = {0, 1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_2359090, Set.ext_iff]

lemma frame_3_2359090.box_zero_one :
    frame_3_2359090.box ({0, 1} : Set (Fin 3)) = {1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_2359090, Set.ext_iff] <;> decide

lemma frame_3_2359090.box_zero_two :
    frame_3_2359090.box ({0, 2} : Set (Fin 3)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_2359090]

lemma frame_3_2359090.box_one_two :
    frame_3_2359090.box ({1, 2} : Set (Fin 3)) = {1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_2359090, Set.ext_iff] <;> decide

lemma frame_3_2359090.box_univ :
    frame_3_2359090.box (Set.univ : Set (Fin 3)) = {1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_2359090, Set.ext_iff] <;> decide

lemma frame_3_2359090.compl_zero : ({0} : Set (Fin 3))ᶜ = {1, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_2359090.compl_one : ({1} : Set (Fin 3))ᶜ = {0, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_2359090.compl_two : ({2} : Set (Fin 3))ᶜ = {0, 1} := by
  ext i; fin_cases i <;> simp

lemma frame_3_2359090.compl_zero_one : ({0, 1} : Set (Fin 3))ᶜ = {2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_2359090.compl_zero_two : ({0, 2} : Set (Fin 3))ᶜ = {1} := by
  ext i; fin_cases i <;> simp

lemma frame_3_2359090.compl_one_two : ({1, 2} : Set (Fin 3))ᶜ = {0} := by
  ext i; fin_cases i <;> simp

lemma frame_3_2359090.dia_empty :
    frame_3_2359090.dia (∅ : Set (Fin 3)) = {0, 2} := by
  simp [Frame.dia, frame_3_2359090.box_univ, frame_3_2359090.compl_one]

lemma frame_3_2359090.dia_zero :
    frame_3_2359090.dia ({0} : Set (Fin 3)) = {0, 2} := by
  simp [Frame.dia, frame_3_2359090.compl_zero, frame_3_2359090.box_one_two,
    frame_3_2359090.compl_one]

lemma frame_3_2359090.dia_one :
    frame_3_2359090.dia ({1} : Set (Fin 3)) = ∅ := by
  simp [Frame.dia, frame_3_2359090.compl_one, frame_3_2359090.box_zero_two]

lemma frame_3_2359090.dia_two :
    frame_3_2359090.dia ({2} : Set (Fin 3)) = {0, 2} := by
  simp [Frame.dia, frame_3_2359090.compl_two, frame_3_2359090.box_zero_one,
    frame_3_2359090.compl_one]

lemma frame_3_2359090.dia_zero_one :
    frame_3_2359090.dia ({0, 1} : Set (Fin 3)) = {2} := by
  simp [Frame.dia, frame_3_2359090.compl_zero_one, frame_3_2359090.box_two,
    frame_3_2359090.compl_zero_one]

lemma frame_3_2359090.dia_zero_two :
    frame_3_2359090.dia ({0, 2} : Set (Fin 3)) = {0, 2} := by
  simp [Frame.dia, frame_3_2359090.compl_zero_two, frame_3_2359090.box_one,
    frame_3_2359090.compl_one]

lemma frame_3_2359090.dia_one_two :
    frame_3_2359090.dia ({1, 2} : Set (Fin 3)) = ∅ := by
  simp [Frame.dia, frame_3_2359090.compl_one_two, frame_3_2359090.box_zero]

lemma frame_3_2359090.dia_univ :
    frame_3_2359090.dia (Set.univ : Set (Fin 3)) = {0} := by
  simp [Frame.dia, frame_3_2359090.box_empty, frame_3_2359090.compl_one_two]

instance : frame_3_2359090.IsSymmetric := ⟨fun X => by
  by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X
  · have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_2359090.dia_univ, frame_3_2359090.box_zero]
  · have hX : X = ({0, 1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_2359090.dia_zero_one, frame_3_2359090.box_two]
  · have hX : X = ({0, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_2359090.dia_zero_two, frame_3_2359090.box_zero_two]
  · have hX : X = ({0} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_2359090.dia_zero, frame_3_2359090.box_zero_two]
  · have hX : X = ({1, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_2359090.dia_one_two, frame_3_2359090.box_empty]
  · have hX : X = ({1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_2359090.dia_one, frame_3_2359090.box_empty]
  · have hX : X = ({2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_2359090.dia_two, frame_3_2359090.box_zero_two]
  · have hX : X = (∅ : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_2359090.dia_empty, frame_3_2359090.box_zero_two]⟩

@[simp]
lemma frame_3_2359090.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_2359090 ⊧ (Axioms.C #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0} else if c = b then {2} else Set.univ, 0, by
      unfold NotForces Forces
      simp only [Model.truthset.eq_imp, Model.truthset.eq_box,
        Model.truthset.eq_atom, Set.mem_compl_iff, Set.mem_union, not_or, not_not]
      simp [Frame.box, frame_3_2359090, Ne.symm hab, Set.ext_iff]
      decide⟩

end
