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
variable {a : α}

abbrev frame_4_9872034215406635472 : Frame (Fin 4) :=
  ⟨fun w => match w with
    | 0 => {{2}, {1, 2}, {0, 1, 2}, {3}, {0, 1, 3}, Set.univ}
    | 1 => {{2}, {1, 2}, {0, 1, 2}, {3}, {0, 3}, {0, 1, 3}, Set.univ}
    | 2 => {{2}, {1, 2}, {0, 1, 2}, {0, 3}, Set.univ}
    | 3 => {{3}, {0, 1, 3}, Set.univ}⟩

instance : frame_4_9872034215406635472.NotContainsEmpty := ⟨fun x => by
  fin_cases x <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] <;>
    and_intros <;>
    first
      | exact (Set.singleton_ne_empty _).symm
      | exact (Set.insert_nonempty _ _).ne_empty.symm
      | exact (Set.univ_nonempty (α := Fin 4)).ne_empty.symm⟩

lemma frame_4_9872034215406635472.box_empty :
    frame_4_9872034215406635472.box (∅ : Set (Fin 4)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff] <;> decide

lemma frame_4_9872034215406635472.box_zero :
    frame_4_9872034215406635472.box ({0} : Set (Fin 4)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff] <;> decide

lemma frame_4_9872034215406635472.box_one :
    frame_4_9872034215406635472.box ({1} : Set (Fin 4)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff] <;> decide

lemma frame_4_9872034215406635472.box_two :
    frame_4_9872034215406635472.box ({2} : Set (Fin 4)) = {0, 1, 2} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff]; decide

lemma frame_4_9872034215406635472.box_three :
    frame_4_9872034215406635472.box ({3} : Set (Fin 4)) = {0, 1, 3} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff]; decide

lemma frame_4_9872034215406635472.box_zero_one :
    frame_4_9872034215406635472.box ({0, 1} : Set (Fin 4)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff] <;> decide

lemma frame_4_9872034215406635472.box_zero_two :
    frame_4_9872034215406635472.box ({0, 2} : Set (Fin 4)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff] <;> decide

lemma frame_4_9872034215406635472.box_zero_three :
    frame_4_9872034215406635472.box ({0, 3} : Set (Fin 4)) = {1, 2} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff] <;> decide

lemma frame_4_9872034215406635472.box_one_two :
    frame_4_9872034215406635472.box ({1, 2} : Set (Fin 4)) = {0, 1, 2} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff]; decide

lemma frame_4_9872034215406635472.box_one_three :
    frame_4_9872034215406635472.box ({1, 3} : Set (Fin 4)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff] <;> decide

lemma frame_4_9872034215406635472.box_two_three :
    frame_4_9872034215406635472.box ({2, 3} : Set (Fin 4)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff] <;> decide

lemma frame_4_9872034215406635472.box_zero_one_two :
    frame_4_9872034215406635472.box ({0, 1, 2} : Set (Fin 4)) = {0, 1, 2} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff]; decide

lemma frame_4_9872034215406635472.box_zero_one_three :
    frame_4_9872034215406635472.box ({0, 1, 3} : Set (Fin 4)) = {0, 1, 3} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff]; decide

lemma frame_4_9872034215406635472.box_zero_two_three :
    frame_4_9872034215406635472.box ({0, 2, 3} : Set (Fin 4)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff] <;> decide

lemma frame_4_9872034215406635472.box_one_two_three :
    frame_4_9872034215406635472.box ({1, 2, 3} : Set (Fin 4)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472, Set.ext_iff] <;> decide

lemma frame_4_9872034215406635472.box_univ :
    frame_4_9872034215406635472.box (Set.univ : Set (Fin 4)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_9872034215406635472]

lemma frame_4_9872034215406635472.compl_zero : ({0} : Set (Fin 4))ᶜ = {1, 2, 3} := by
  ext i; fin_cases i <;> simp

lemma frame_4_9872034215406635472.compl_one : ({1} : Set (Fin 4))ᶜ = {0, 2, 3} := by
  ext i; fin_cases i <;> simp

lemma frame_4_9872034215406635472.compl_two : ({2} : Set (Fin 4))ᶜ = {0, 1, 3} := by
  ext i; fin_cases i <;> simp

lemma frame_4_9872034215406635472.compl_three : ({3} : Set (Fin 4))ᶜ = {0, 1, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_4_9872034215406635472.compl_zero_one : ({0, 1} : Set (Fin 4))ᶜ = {2, 3} := by
  ext i; fin_cases i <;> simp

lemma frame_4_9872034215406635472.compl_zero_two : ({0, 2} : Set (Fin 4))ᶜ = {1, 3} := by
  ext i; fin_cases i <;> simp

lemma frame_4_9872034215406635472.compl_zero_three : ({0, 3} : Set (Fin 4))ᶜ = {1, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_4_9872034215406635472.compl_one_two : ({1, 2} : Set (Fin 4))ᶜ = {0, 3} := by
  ext i; fin_cases i <;> simp

lemma frame_4_9872034215406635472.compl_one_three : ({1, 3} : Set (Fin 4))ᶜ = {0, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_4_9872034215406635472.compl_two_three : ({2, 3} : Set (Fin 4))ᶜ = {0, 1} := by
  ext i; fin_cases i <;> simp

lemma frame_4_9872034215406635472.compl_zero_one_two : ({0, 1, 2} : Set (Fin 4))ᶜ = {3} := by
  ext i; fin_cases i <;> simp

lemma frame_4_9872034215406635472.compl_zero_one_three : ({0, 1, 3} : Set (Fin 4))ᶜ = {2} := by
  ext i; fin_cases i <;> simp

lemma frame_4_9872034215406635472.compl_zero_two_three : ({0, 2, 3} : Set (Fin 4))ᶜ = {1} := by
  ext i; fin_cases i <;> simp

lemma frame_4_9872034215406635472.compl_one_two_three : ({1, 2, 3} : Set (Fin 4))ᶜ = {0} := by
  ext i; fin_cases i <;> simp

lemma frame_4_9872034215406635472.dia_empty :
    frame_4_9872034215406635472.dia (∅ : Set (Fin 4)) = ∅ := by
  simp [Frame.dia, frame_4_9872034215406635472.box_univ]

lemma frame_4_9872034215406635472.dia_zero :
    frame_4_9872034215406635472.dia ({0} : Set (Fin 4)) = Set.univ := by
  simp [Frame.dia, frame_4_9872034215406635472.compl_zero,
    frame_4_9872034215406635472.box_one_two_three]

lemma frame_4_9872034215406635472.dia_one :
    frame_4_9872034215406635472.dia ({1} : Set (Fin 4)) = Set.univ := by
  simp [Frame.dia, frame_4_9872034215406635472.compl_one,
    frame_4_9872034215406635472.box_zero_two_three]

lemma frame_4_9872034215406635472.dia_two :
    frame_4_9872034215406635472.dia ({2} : Set (Fin 4)) = {2} := by
  simp [Frame.dia, frame_4_9872034215406635472.compl_two,
    frame_4_9872034215406635472.box_zero_one_three, frame_4_9872034215406635472.compl_zero_one_three]

lemma frame_4_9872034215406635472.dia_three :
    frame_4_9872034215406635472.dia ({3} : Set (Fin 4)) = {3} := by
  simp [Frame.dia, frame_4_9872034215406635472.compl_three,
    frame_4_9872034215406635472.box_zero_one_two, frame_4_9872034215406635472.compl_zero_one_two]

lemma frame_4_9872034215406635472.dia_zero_one :
    frame_4_9872034215406635472.dia ({0, 1} : Set (Fin 4)) = Set.univ := by
  simp [Frame.dia, frame_4_9872034215406635472.compl_zero_one,
    frame_4_9872034215406635472.box_two_three]

lemma frame_4_9872034215406635472.dia_zero_two :
    frame_4_9872034215406635472.dia ({0, 2} : Set (Fin 4)) = Set.univ := by
  simp [Frame.dia, frame_4_9872034215406635472.compl_zero_two,
    frame_4_9872034215406635472.box_one_three]

lemma frame_4_9872034215406635472.dia_zero_three :
    frame_4_9872034215406635472.dia ({0, 3} : Set (Fin 4)) = {3} := by
  simp [Frame.dia, frame_4_9872034215406635472.compl_zero_three,
    frame_4_9872034215406635472.box_one_two, frame_4_9872034215406635472.compl_zero_one_two]

lemma frame_4_9872034215406635472.dia_one_two :
    frame_4_9872034215406635472.dia ({1, 2} : Set (Fin 4)) = {0, 3} := by
  simp [Frame.dia, frame_4_9872034215406635472.compl_one_two,
    frame_4_9872034215406635472.box_zero_three]

lemma frame_4_9872034215406635472.dia_one_three :
    frame_4_9872034215406635472.dia ({1, 3} : Set (Fin 4)) = Set.univ := by
  simp [Frame.dia, frame_4_9872034215406635472.compl_one_three,
    frame_4_9872034215406635472.box_zero_two]

lemma frame_4_9872034215406635472.dia_two_three :
    frame_4_9872034215406635472.dia ({2, 3} : Set (Fin 4)) = Set.univ := by
  simp [Frame.dia, frame_4_9872034215406635472.compl_two_three,
    frame_4_9872034215406635472.box_zero_one]

lemma frame_4_9872034215406635472.dia_zero_one_two :
    frame_4_9872034215406635472.dia ({0, 1, 2} : Set (Fin 4)) = {2} := by
  simp [Frame.dia, frame_4_9872034215406635472.compl_zero_one_two,
    frame_4_9872034215406635472.box_three, frame_4_9872034215406635472.compl_zero_one_three]

lemma frame_4_9872034215406635472.dia_zero_one_three :
    frame_4_9872034215406635472.dia ({0, 1, 3} : Set (Fin 4)) = {3} := by
  simp [Frame.dia, frame_4_9872034215406635472.compl_zero_one_three,
    frame_4_9872034215406635472.box_two, frame_4_9872034215406635472.compl_zero_one_two]

lemma frame_4_9872034215406635472.dia_zero_two_three :
    frame_4_9872034215406635472.dia ({0, 2, 3} : Set (Fin 4)) = Set.univ := by
  simp [Frame.dia, frame_4_9872034215406635472.compl_zero_two_three,
    frame_4_9872034215406635472.box_one]

lemma frame_4_9872034215406635472.dia_one_two_three :
    frame_4_9872034215406635472.dia ({1, 2, 3} : Set (Fin 4)) = Set.univ := by
  simp [Frame.dia, frame_4_9872034215406635472.compl_one_two_three,
    frame_4_9872034215406635472.box_zero]

lemma frame_4_9872034215406635472.dia_univ :
    frame_4_9872034215406635472.dia (Set.univ : Set (Fin 4)) = Set.univ := by
  simp [Frame.dia, frame_4_9872034215406635472.box_empty]

instance : frame_4_9872034215406635472.IsTransitive where
  trans X := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    by_cases h0 : (0 : Fin 4) ∈ X <;> by_cases h1 : (1 : Fin 4) ∈ X <;>
      by_cases h2 : (2 : Fin 4) ∈ X <;> by_cases h3 : (3 : Fin 4) ∈ X
    · have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_univ]
    · have hX : X = ({0, 1, 2} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_zero_one_two]
    · have hX : X = ({0, 1, 3} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_zero_one_three]
    · have hX : X = ({0, 1} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_zero_one, frame_4_9872034215406635472.box_empty]
    · have hX : X = ({0, 2, 3} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_zero_two_three, frame_4_9872034215406635472.box_empty]
    · have hX : X = ({0, 2} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_zero_two, frame_4_9872034215406635472.box_empty]
    · have hX : X = ({0, 3} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_zero_three, frame_4_9872034215406635472.box_one_two]
    · have hX : X = ({0} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_zero, frame_4_9872034215406635472.box_empty]
    · have hX : X = ({1, 2, 3} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_one_two_three, frame_4_9872034215406635472.box_empty]
    · have hX : X = ({1, 2} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_one_two, frame_4_9872034215406635472.box_zero_one_two]
    · have hX : X = ({1, 3} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_one_three, frame_4_9872034215406635472.box_empty]
    · have hX : X = ({1} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_one, frame_4_9872034215406635472.box_empty]
    · have hX : X = ({2, 3} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_two_three, frame_4_9872034215406635472.box_empty]
    · have hX : X = ({2} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_two, frame_4_9872034215406635472.box_zero_one_two]
    · have hX : X = ({3} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_three, frame_4_9872034215406635472.box_zero_one_three]
    · have hX : X = (∅ : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
      subst hX; simp [frame_4_9872034215406635472.box_empty]

instance : frame_4_9872034215406635472.IsSymmetric := ⟨fun X => by
  by_cases h0 : (0 : Fin 4) ∈ X <;> by_cases h1 : (1 : Fin 4) ∈ X <;>
    by_cases h2 : (2 : Fin 4) ∈ X <;> by_cases h3 : (3 : Fin 4) ∈ X
  · have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_4_9872034215406635472.dia_univ, frame_4_9872034215406635472.box_univ]
  · have hX : X = ({0, 1, 2} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX
    simp [frame_4_9872034215406635472.dia_zero_one_two, frame_4_9872034215406635472.box_two]
  · have hX : X = ({0, 1, 3} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX
    simp [frame_4_9872034215406635472.dia_zero_one_three, frame_4_9872034215406635472.box_three]
  · have hX : X = ({0, 1} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_4_9872034215406635472.dia_zero_one, frame_4_9872034215406635472.box_univ]
  · have hX : X = ({0, 2, 3} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX
    simp [frame_4_9872034215406635472.dia_zero_two_three, frame_4_9872034215406635472.box_univ]
  · have hX : X = ({0, 2} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_4_9872034215406635472.dia_zero_two, frame_4_9872034215406635472.box_univ]
  · have hX : X = ({0, 3} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_4_9872034215406635472.dia_zero_three, frame_4_9872034215406635472.box_three]
  · have hX : X = ({0} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_4_9872034215406635472.dia_zero, frame_4_9872034215406635472.box_univ]
  · have hX : X = ({1, 2, 3} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX
    simp [frame_4_9872034215406635472.dia_one_two_three, frame_4_9872034215406635472.box_univ]
  · have hX : X = ({1, 2} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_4_9872034215406635472.dia_one_two, frame_4_9872034215406635472.box_zero_three]
  · have hX : X = ({1, 3} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_4_9872034215406635472.dia_one_three, frame_4_9872034215406635472.box_univ]
  · have hX : X = ({1} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_4_9872034215406635472.dia_one, frame_4_9872034215406635472.box_univ]
  · have hX : X = ({2, 3} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_4_9872034215406635472.dia_two_three, frame_4_9872034215406635472.box_univ]
  · have hX : X = ({2} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_4_9872034215406635472.dia_two, frame_4_9872034215406635472.box_two]
  · have hX : X = ({3} : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_4_9872034215406635472.dia_three, frame_4_9872034215406635472.box_three]
  · have hX : X = (∅ : Set (Fin 4)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_4_9872034215406635472.dia_empty, frame_4_9872034215406635472.box_empty]⟩

lemma frame_4_9872034215406635472.not_isEuclidean :
    ¬frame_4_9872034215406635472.IsEuclidean := fun hE => by
  have h := hE.eucl ({1, 2} : Set (Fin 4))
  rw [frame_4_9872034215406635472.dia_one_two, frame_4_9872034215406635472.box_zero_three] at h
  exact absurd (h (show (0 : Fin 4) ∈ ({0, 3} : Set (Fin 4)) by simp)) (by simp)

lemma frame_4_9872034215406635472.not_valid_axiomFive :
    ¬frame_4_9872034215406635472 ⊧ (Axioms.Five #a : Formula α) :=
  fun h => frame_4_9872034215406635472.not_isEuclidean (isEuclidean_of_valid_axiomFive h)

end
