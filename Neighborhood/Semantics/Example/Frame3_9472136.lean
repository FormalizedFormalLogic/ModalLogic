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

abbrev frame_3_9472136 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0, 1}, Set.univ}
    | 1 => {{0, 1}, Set.univ}
    | 2 => {{2}, Set.univ}⟩

instance : frame_3_9472136.NotContainsEmpty := ⟨fun x => by
  fin_cases x <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  · exact ⟨(Set.insert_nonempty _ _).ne_empty.symm, Set.univ_nonempty.ne_empty.symm⟩
  · exact ⟨(Set.insert_nonempty _ _).ne_empty.symm, Set.univ_nonempty.ne_empty.symm⟩
  · exact ⟨(Set.singleton_nonempty _).ne_empty.symm, Set.univ_nonempty.ne_empty.symm⟩⟩

instance : frame_3_9472136.IsRegular where
  regular X Y := by
    intro x ⟨hX, hY⟩
    fin_cases x <;>
      simp only [Frame.box, frame_3_9472136, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hX hY ⊢ <;>
      rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp

instance : frame_3_9472136.IsReflexive where
  refl X w hw := by
    fin_cases w <;>
      simp only [Frame.box, frame_3_9472136, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢ <;>
      rcases hw with rfl | rfl <;> simp

lemma frame_3_9472136.box_empty :
    frame_3_9472136.box (∅ : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9472136, Set.ext_iff] <;> decide

lemma frame_3_9472136.box_singleton_zero :
    frame_3_9472136.box ({0} : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9472136, Set.ext_iff] <;> decide

lemma frame_3_9472136.box_singleton_one :
    frame_3_9472136.box ({1} : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9472136, Set.ext_iff] <;> decide

lemma frame_3_9472136.box_singleton_two :
    frame_3_9472136.box ({2} : Set (Fin 3)) = {2} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9472136, Set.ext_iff] <;> decide

lemma frame_3_9472136.box_zero_one :
    frame_3_9472136.box ({0, 1} : Set (Fin 3)) = {0, 1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9472136, Set.ext_iff]; decide

lemma frame_3_9472136.box_zero_two :
    frame_3_9472136.box ({0, 2} : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9472136, Set.ext_iff] <;> decide

lemma frame_3_9472136.box_one_two :
    frame_3_9472136.box ({1, 2} : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9472136, Set.ext_iff] <;> decide

lemma frame_3_9472136.box_univ :
    frame_3_9472136.box (Set.univ : Set (Fin 3)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9472136]

lemma frame_3_9472136.compl_zero : ({0} : Set (Fin 3))ᶜ = {1, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_9472136.compl_one : ({1} : Set (Fin 3))ᶜ = {0, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_9472136.compl_two : ({2} : Set (Fin 3))ᶜ = {0, 1} := by
  ext i; fin_cases i <;> simp

lemma frame_3_9472136.compl_zero_one : ({0, 1} : Set (Fin 3))ᶜ = {2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_9472136.compl_zero_two : ({0, 2} : Set (Fin 3))ᶜ = {1} := by
  ext i; fin_cases i <;> simp

lemma frame_3_9472136.compl_one_two : ({1, 2} : Set (Fin 3))ᶜ = {0} := by
  ext i; fin_cases i <;> simp

lemma frame_3_9472136.dia_empty :
    frame_3_9472136.dia (∅ : Set (Fin 3)) = ∅ := by
  simp [Frame.dia, frame_3_9472136.box_univ]

lemma frame_3_9472136.dia_zero :
    frame_3_9472136.dia ({0} : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_9472136.compl_zero, frame_3_9472136.box_one_two]

lemma frame_3_9472136.dia_one :
    frame_3_9472136.dia ({1} : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_9472136.compl_one, frame_3_9472136.box_zero_two]

lemma frame_3_9472136.dia_two :
    frame_3_9472136.dia ({2} : Set (Fin 3)) = {2} := by
  simp [Frame.dia, frame_3_9472136.compl_two, frame_3_9472136.box_zero_one,
    frame_3_9472136.compl_zero_one]

lemma frame_3_9472136.dia_zero_one :
    frame_3_9472136.dia ({0, 1} : Set (Fin 3)) = {0, 1} := by
  simp [Frame.dia, frame_3_9472136.compl_zero_one, frame_3_9472136.box_singleton_two,
    frame_3_9472136.compl_two]

lemma frame_3_9472136.dia_zero_two :
    frame_3_9472136.dia ({0, 2} : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_9472136.compl_zero_two, frame_3_9472136.box_singleton_one]

lemma frame_3_9472136.dia_one_two :
    frame_3_9472136.dia ({1, 2} : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_9472136.compl_one_two, frame_3_9472136.box_singleton_zero]

lemma frame_3_9472136.dia_univ :
    frame_3_9472136.dia (Set.univ : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_9472136.box_empty]

instance : frame_3_9472136.IsEuclidean := ⟨fun X => by
  by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X
  · have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_univ, frame_3_9472136.box_univ]
  · have hX : X = ({0, 1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_zero_one, frame_3_9472136.box_zero_one]
  · have hX : X = ({0, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_zero_two, frame_3_9472136.box_univ]
  · have hX : X = ({0} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_zero, frame_3_9472136.box_univ]
  · have hX : X = ({1, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_one_two, frame_3_9472136.box_univ]
  · have hX : X = ({1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_one, frame_3_9472136.box_univ]
  · have hX : X = ({2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_two, frame_3_9472136.box_singleton_two]
  · have hX : X = (∅ : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_empty, frame_3_9472136.box_empty]⟩

instance : frame_3_9472136.IsSymmetric := ⟨fun X => by
  by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X
  · have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_univ, frame_3_9472136.box_univ]
  · have hX : X = ({0, 1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_zero_one, frame_3_9472136.box_zero_one]
  · have hX : X = ({0, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_zero_two, frame_3_9472136.box_univ]
  · have hX : X = ({0} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_zero, frame_3_9472136.box_univ]
  · have hX : X = ({1, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_one_two, frame_3_9472136.box_univ]
  · have hX : X = ({1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_one, frame_3_9472136.box_univ]
  · have hX : X = ({2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_two, frame_3_9472136.box_singleton_two]
  · have hX : X = (∅ : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9472136.dia_empty, frame_3_9472136.box_empty]⟩

instance : frame_3_9472136.ContainsUnit := ⟨frame_3_9472136.box_univ⟩

instance : frame_3_9472136.IsSerial where
  serial X w hw := by
    have hw' : X ∈ frame_3_9472136.𝒩 w := hw
    fin_cases w <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
    · rcases hw' with rfl | rfl
      · simp [frame_3_9472136.dia_zero_one]
      · simp [frame_3_9472136.dia_univ]
    · rcases hw' with rfl | rfl
      · simp [frame_3_9472136.dia_zero_one]
      · simp [frame_3_9472136.dia_univ]
    · rcases hw' with rfl | rfl
      · simp [frame_3_9472136.dia_two]
      · simp [frame_3_9472136.dia_univ]

instance : frame_3_9472136.IsTransitive where
  trans X := by
    by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X
    · have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
      subst hX; simp [Function.iterate_succ, frame_3_9472136.box_univ]
    · have hX : X = ({0, 1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [Function.iterate_succ, frame_3_9472136.box_zero_one]
    · have hX : X = ({0, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [Function.iterate_succ, frame_3_9472136.box_zero_two,
        frame_3_9472136.box_empty]
    · have hX : X = ({0} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [Function.iterate_succ,
        frame_3_9472136.box_singleton_zero, frame_3_9472136.box_empty]
    · have hX : X = ({1, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [Function.iterate_succ, frame_3_9472136.box_one_two,
        frame_3_9472136.box_empty]
    · have hX : X = ({1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [Function.iterate_succ,
        frame_3_9472136.box_singleton_one, frame_3_9472136.box_empty]
    · have hX : X = ({2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [Function.iterate_succ,
        frame_3_9472136.box_singleton_two]
    · have hX : X = (∅ : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [Function.iterate_succ, frame_3_9472136.box_empty]

@[simp]
lemma frame_3_9472136.not_valid_axiomK [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_9472136 ⊧ (Axioms.K #a #b : Formula α) := fun h => by
  have h0 := h (fun c => if c = a then {2} else if c = b then {0, 2} else Set.univ) 2
  simp [Forces, Frame.box, Set.ext_iff, Ne.symm hab] at h0
  revert h0
  decide

@[simp]
lemma frame_3_9472136.not_valid_axiomM [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_9472136 ⊧ (Axioms.M #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0, 2} else if c = b then {2} else Set.univ, 2, by
      unfold NotForces Forces; simp [Frame.box, frame_3_9472136, Set.ext_iff, Ne.symm hab]; decide⟩

end
