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

abbrev frame_3_9488552 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0, 1}, {0, 2}, Set.univ}
    | 1 => {{0, 1}, {1, 2}, Set.univ}
    | 2 => {{2}, Set.univ}⟩

lemma frame_3_9488552.box_empty :
    frame_3_9488552.box (∅ : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9488552, Set.ext_iff] <;> decide

lemma frame_3_9488552.box_singleton_zero :
    frame_3_9488552.box ({0} : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9488552, Set.ext_iff] <;> decide

lemma frame_3_9488552.box_singleton_one :
    frame_3_9488552.box ({1} : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9488552, Set.ext_iff] <;> decide

lemma frame_3_9488552.box_singleton_two :
    frame_3_9488552.box ({2} : Set (Fin 3)) = {2} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9488552, Set.ext_iff] <;> decide

lemma frame_3_9488552.box_zero_one :
    frame_3_9488552.box ({0, 1} : Set (Fin 3)) = {0, 1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9488552, Set.ext_iff]; decide

lemma frame_3_9488552.box_zero_two :
    frame_3_9488552.box ({0, 2} : Set (Fin 3)) = {0} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9488552, Set.ext_iff] <;> decide

lemma frame_3_9488552.box_one_two :
    frame_3_9488552.box ({1, 2} : Set (Fin 3)) = {1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9488552, Set.ext_iff] <;> decide

lemma frame_3_9488552.box_univ :
    frame_3_9488552.box (Set.univ : Set (Fin 3)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_9488552]

instance : frame_3_9488552.NotContainsEmpty := ⟨fun x => by
  fin_cases x <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] <;>
    (and_intros <;>
      first
        | exact (Set.insert_nonempty _ _).ne_empty.symm
        | exact (Set.singleton_nonempty _).ne_empty.symm
        | exact Set.univ_nonempty.ne_empty.symm)⟩

instance : frame_3_9488552.IsReflexive where
  refl X w hw := by
    fin_cases w <;>
      simp only [Frame.box, frame_3_9488552, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢ <;>
      rcases hw with rfl | rfl | rfl <;> simp

lemma frame_3_9488552.compl_zero : ({0} : Set (Fin 3))ᶜ = {1, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_9488552.compl_one : ({1} : Set (Fin 3))ᶜ = {0, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_9488552.compl_two : ({2} : Set (Fin 3))ᶜ = {0, 1} := by
  ext i; fin_cases i <;> simp

lemma frame_3_9488552.compl_zero_one : ({0, 1} : Set (Fin 3))ᶜ = {2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_9488552.compl_zero_two : ({0, 2} : Set (Fin 3))ᶜ = {1} := by
  ext i; fin_cases i <;> simp

lemma frame_3_9488552.compl_one_two : ({1, 2} : Set (Fin 3))ᶜ = {0} := by
  ext i; fin_cases i <;> simp

lemma frame_3_9488552.dia_empty :
    frame_3_9488552.dia (∅ : Set (Fin 3)) = ∅ := by
  simp [Frame.dia, frame_3_9488552.box_univ]

lemma frame_3_9488552.dia_zero :
    frame_3_9488552.dia ({0} : Set (Fin 3)) = {0, 2} := by
  simp [Frame.dia, frame_3_9488552.compl_zero, frame_3_9488552.box_one_two,
    frame_3_9488552.compl_one]

lemma frame_3_9488552.dia_one :
    frame_3_9488552.dia ({1} : Set (Fin 3)) = {1, 2} := by
  simp [Frame.dia, frame_3_9488552.compl_one, frame_3_9488552.box_zero_two,
    frame_3_9488552.compl_zero]

lemma frame_3_9488552.dia_two :
    frame_3_9488552.dia ({2} : Set (Fin 3)) = {2} := by
  simp [Frame.dia, frame_3_9488552.compl_two, frame_3_9488552.box_zero_one,
    frame_3_9488552.compl_zero_one]

lemma frame_3_9488552.dia_zero_one :
    frame_3_9488552.dia ({0, 1} : Set (Fin 3)) = {0, 1} := by
  simp [Frame.dia, frame_3_9488552.compl_zero_one, frame_3_9488552.box_singleton_two,
    frame_3_9488552.compl_two]

lemma frame_3_9488552.dia_zero_two :
    frame_3_9488552.dia ({0, 2} : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_9488552.compl_zero_two, frame_3_9488552.box_singleton_one]

lemma frame_3_9488552.dia_one_two :
    frame_3_9488552.dia ({1, 2} : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_9488552.compl_one_two, frame_3_9488552.box_singleton_zero]

lemma frame_3_9488552.dia_univ :
    frame_3_9488552.dia (Set.univ : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_9488552.box_empty]

instance : frame_3_9488552.IsSymmetric := ⟨fun X => by
  by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X
  · have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9488552.dia_univ, frame_3_9488552.box_univ]
  · have hX : X = ({0, 1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9488552.dia_zero_one, frame_3_9488552.box_zero_one]
  · have hX : X = ({0, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9488552.dia_zero_two, frame_3_9488552.box_univ]
  · have hX : X = ({0} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9488552.dia_zero, frame_3_9488552.box_zero_two]
  · have hX : X = ({1, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9488552.dia_one_two, frame_3_9488552.box_univ]
  · have hX : X = ({1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9488552.dia_one, frame_3_9488552.box_one_two]
  · have hX : X = ({2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9488552.dia_two, frame_3_9488552.box_singleton_two]
  · have hX : X = (∅ : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_9488552.dia_empty, frame_3_9488552.box_empty]⟩

lemma frame_3_9488552.not_isRegular :
    ¬frame_3_9488552.IsRegular := by
  intro hR
  have h := hR.regular ({0, 1} : Set (Fin 3)) ({0, 2} : Set (Fin 3))
  have h0 : (0 : Fin 3) ∈ frame_3_9488552.box {0, 1} ∩ frame_3_9488552.box {0, 2} := by
    rw [frame_3_9488552.box_zero_one, frame_3_9488552.box_zero_two]; simp
  have hmem := h h0
  have heq : ({0, 1} : Set (Fin 3)) ∩ {0, 2} = {0} := by ext i; fin_cases i <;> simp
  rw [heq, frame_3_9488552.box_singleton_zero] at hmem
  simp at hmem

instance : frame_3_9488552.ContainsUnit := ⟨frame_3_9488552.box_univ⟩

instance : frame_3_9488552.IsSerial where
  serial X w hw := by
    have hw' : X ∈ frame_3_9488552.𝒩 w := hw
    fin_cases w <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
    · rcases hw' with rfl | rfl | rfl
      · simp [frame_3_9488552.dia_zero_one]
      · simp [frame_3_9488552.dia_zero_two]
      · simp [frame_3_9488552.dia_univ]
    · rcases hw' with rfl | rfl | rfl
      · simp [frame_3_9488552.dia_zero_one]
      · simp [frame_3_9488552.dia_one_two]
      · simp [frame_3_9488552.dia_univ]
    · rcases hw' with rfl | rfl
      · simp [frame_3_9488552.dia_two]
      · simp [frame_3_9488552.dia_univ]

lemma frame_3_9488552.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_9488552 ⊧ (Axioms.C #a #b : Formula α) := by
  intro hv
  apply frame_3_9488552.not_isRegular
  constructor
  rintro X Y x ⟨hX, hY⟩
  have h₂ := hv (fun c => if c = a then X else if c = b then Y else ∅) x
  rw [forces_imp, forces_and, forces_box, forces_box, forces_box, Model.truthset.eq_and] at h₂
  simp only [Model.truthset.eq_atom, if_neg (Ne.symm hab)] at h₂
  exact h₂ ⟨hX, hY⟩

end
