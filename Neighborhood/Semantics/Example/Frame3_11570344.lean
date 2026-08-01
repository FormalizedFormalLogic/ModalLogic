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

abbrev frame_3_11570344 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0, 1}, {0, 2}, Set.univ}
    | 1 => {{1}, {0, 1}, Set.univ}
    | 2 => {{2}, {0, 2}, Set.univ}⟩

lemma frame_3_11570344.box_empty :
    frame_3_11570344.box (∅ : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_11570344, Set.ext_iff] <;> decide

lemma frame_3_11570344.box_singleton_zero :
    frame_3_11570344.box ({0} : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_11570344, Set.ext_iff] <;> decide

lemma frame_3_11570344.box_singleton_one :
    frame_3_11570344.box ({1} : Set (Fin 3)) = {1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_11570344, Set.ext_iff] <;> decide

lemma frame_3_11570344.box_singleton_two :
    frame_3_11570344.box ({2} : Set (Fin 3)) = {2} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_11570344, Set.ext_iff] <;> decide

lemma frame_3_11570344.box_zero_one :
    frame_3_11570344.box ({0, 1} : Set (Fin 3)) = {0, 1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_11570344, Set.ext_iff]; decide

lemma frame_3_11570344.box_zero_two :
    frame_3_11570344.box ({0, 2} : Set (Fin 3)) = {0, 2} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_11570344, Set.ext_iff]; decide

lemma frame_3_11570344.box_one_two :
    frame_3_11570344.box ({1, 2} : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_11570344, Set.ext_iff] <;> decide

lemma frame_3_11570344.box_univ :
    frame_3_11570344.box (Set.univ : Set (Fin 3)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_11570344]

instance : frame_3_11570344.ContainsUnit := ⟨frame_3_11570344.box_univ⟩

lemma frame_3_11570344.compl_zero : ({0} : Set (Fin 3))ᶜ = {1, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_11570344.compl_one : ({1} : Set (Fin 3))ᶜ = {0, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_11570344.compl_two : ({2} : Set (Fin 3))ᶜ = {0, 1} := by
  ext i; fin_cases i <;> simp

lemma frame_3_11570344.compl_zero_one : ({0, 1} : Set (Fin 3))ᶜ = {2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_11570344.compl_zero_two : ({0, 2} : Set (Fin 3))ᶜ = {1} := by
  ext i; fin_cases i <;> simp

lemma frame_3_11570344.compl_one_two : ({1, 2} : Set (Fin 3))ᶜ = {0} := by
  ext i; fin_cases i <;> simp

lemma frame_3_11570344.dia_empty :
    frame_3_11570344.dia (∅ : Set (Fin 3)) = ∅ := by
  simp [Frame.dia, frame_3_11570344.box_univ]

lemma frame_3_11570344.dia_zero :
    frame_3_11570344.dia ({0} : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_11570344.compl_zero, frame_3_11570344.box_one_two]

lemma frame_3_11570344.dia_one :
    frame_3_11570344.dia ({1} : Set (Fin 3)) = {1} := by
  simp [Frame.dia, frame_3_11570344.compl_one, frame_3_11570344.box_zero_two,
    frame_3_11570344.compl_zero_two]

lemma frame_3_11570344.dia_two :
    frame_3_11570344.dia ({2} : Set (Fin 3)) = {2} := by
  simp [Frame.dia, frame_3_11570344.compl_two, frame_3_11570344.box_zero_one,
    frame_3_11570344.compl_zero_one]

lemma frame_3_11570344.dia_zero_one :
    frame_3_11570344.dia ({0, 1} : Set (Fin 3)) = {0, 1} := by
  simp [Frame.dia, frame_3_11570344.compl_zero_one, frame_3_11570344.box_singleton_two,
    frame_3_11570344.compl_two]

lemma frame_3_11570344.dia_zero_two :
    frame_3_11570344.dia ({0, 2} : Set (Fin 3)) = {0, 2} := by
  simp [Frame.dia, frame_3_11570344.compl_zero_two, frame_3_11570344.box_singleton_one,
    frame_3_11570344.compl_one]

lemma frame_3_11570344.dia_one_two :
    frame_3_11570344.dia ({1, 2} : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_11570344.compl_one_two, frame_3_11570344.box_singleton_zero]

lemma frame_3_11570344.dia_univ :
    frame_3_11570344.dia (Set.univ : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_11570344.box_empty]

instance : frame_3_11570344.IsReflexive where
  refl X w hw := by
    by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X <;>
    first
      | (have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
         subst hX; simp_all [frame_3_11570344.box_univ])
      | (have hX : X = ({0, 1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
         subst hX; simp_all [frame_3_11570344.box_zero_one])
      | (have hX : X = ({0, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
         subst hX; simp_all [frame_3_11570344.box_zero_two])
      | (have hX : X = ({0} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
         subst hX; simp_all [frame_3_11570344.box_singleton_zero])
      | (have hX : X = ({1, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
         subst hX; simp_all [frame_3_11570344.box_one_two])
      | (have hX : X = ({1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
         subst hX; simp_all [frame_3_11570344.box_singleton_one])
      | (have hX : X = ({2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
         subst hX; simp_all [frame_3_11570344.box_singleton_two])
      | (have hX : X = (∅ : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
         subst hX; simp_all [frame_3_11570344.box_empty])

instance : frame_3_11570344.IsSymmetric := ⟨fun X => by
  by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X
  · have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_univ, frame_3_11570344.box_univ]
  · have hX : X = ({0, 1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_zero_one, frame_3_11570344.box_zero_one]
  · have hX : X = ({0, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_zero_two, frame_3_11570344.box_zero_two]
  · have hX : X = ({0} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_zero, frame_3_11570344.box_univ]
  · have hX : X = ({1, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_one_two, frame_3_11570344.box_univ]
  · have hX : X = ({1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_one, frame_3_11570344.box_singleton_one]
  · have hX : X = ({2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_two, frame_3_11570344.box_singleton_two]
  · have hX : X = (∅ : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_empty, frame_3_11570344.box_empty]⟩

instance : frame_3_11570344.IsEuclidean := ⟨fun X => by
  by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X
  · have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_univ, frame_3_11570344.box_univ]
  · have hX : X = ({0, 1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_zero_one, frame_3_11570344.box_zero_one]
  · have hX : X = ({0, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_zero_two, frame_3_11570344.box_zero_two]
  · have hX : X = ({0} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_zero, frame_3_11570344.box_univ]
  · have hX : X = ({1, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_one_two, frame_3_11570344.box_univ]
  · have hX : X = ({1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_one, frame_3_11570344.box_singleton_one]
  · have hX : X = ({2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_two, frame_3_11570344.box_singleton_two]
  · have hX : X = (∅ : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_11570344.dia_empty, frame_3_11570344.box_empty]⟩

instance : frame_3_11570344.IsTransitive where
  trans X := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X
    · have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_3_11570344.box_univ]
    · have hX : X = ({0, 1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_3_11570344.box_zero_one]
    · have hX : X = ({0, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_3_11570344.box_zero_two]
    · have hX : X = ({0} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_3_11570344.box_singleton_zero, frame_3_11570344.box_empty]
    · have hX : X = ({1, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_3_11570344.box_one_two, frame_3_11570344.box_empty]
    · have hX : X = ({1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_3_11570344.box_singleton_one]
    · have hX : X = ({2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_3_11570344.box_singleton_two]
    · have hX : X = (∅ : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_3_11570344.box_empty]

lemma frame_3_11570344.not_isRegular :
    ¬frame_3_11570344.IsRegular := by
  intro hR
  have h := hR.regular ({0, 1} : Set (Fin 3)) ({0, 2} : Set (Fin 3))
  have h0 : (0 : Fin 3) ∈ frame_3_11570344.box {0, 1} ∩ frame_3_11570344.box {0, 2} := by
    rw [frame_3_11570344.box_zero_one, frame_3_11570344.box_zero_two]; simp
  have hmem := h h0
  have heq : ({0, 1} : Set (Fin 3)) ∩ {0, 2} = {0} := by ext i; fin_cases i <;> simp
  rw [heq, frame_3_11570344.box_singleton_zero] at hmem
  simp at hmem

lemma frame_3_11570344.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_11570344 ⊧ (Axioms.C #a #b : Formula α) := by
  intro hv
  apply frame_3_11570344.not_isRegular
  constructor
  rintro X Y x ⟨hX, hY⟩
  have h₂ := hv (fun c => if c = a then X else if c = b then Y else ∅) x
  rw [forces_imp, forces_and, forces_box, forces_box, forces_box, Model.truthset.eq_and] at h₂
  simp only [Model.truthset.eq_atom, if_neg (Ne.symm hab)] at h₂
  exact h₂ ⟨hX, hY⟩

end
