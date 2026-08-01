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

abbrev frame_3_8815746 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0}, Set.univ}
    | 1 => {{1}, Set.univ}
    | 2 => {{0}, {1}, Set.univ}⟩

instance : frame_3_8815746.NotContainsEmpty := ⟨fun x => by
  fin_cases x <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] <;>
    and_intros <;>
    first
      | exact (Set.singleton_ne_empty _).symm
      | exact (Set.insert_nonempty _ _).ne_empty.symm
      | exact (Set.univ_nonempty (α := Fin 3)).ne_empty.symm⟩

lemma frame_3_8815746.box_empty :
    frame_3_8815746.box (∅ : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8815746, Set.ext_iff]

lemma frame_3_8815746.box_zero :
    frame_3_8815746.box ({0} : Set (Fin 3)) = {0, 2} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8815746, Set.ext_iff]; decide

lemma frame_3_8815746.box_one :
    frame_3_8815746.box ({1} : Set (Fin 3)) = {1, 2} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8815746, Set.ext_iff]; decide

lemma frame_3_8815746.box_two :
    frame_3_8815746.box ({2} : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8815746, Set.ext_iff] <;> decide

lemma frame_3_8815746.box_zero_one :
    frame_3_8815746.box ({0, 1} : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8815746, Set.ext_iff] <;> decide

lemma frame_3_8815746.box_zero_two :
    frame_3_8815746.box ({0, 2} : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8815746, Set.ext_iff] <;> decide

lemma frame_3_8815746.box_one_two :
    frame_3_8815746.box ({1, 2} : Set (Fin 3)) = ∅ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8815746, Set.ext_iff] <;> decide

lemma frame_3_8815746.box_univ :
    frame_3_8815746.box (Set.univ : Set (Fin 3)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8815746]

lemma frame_3_8815746.compl_zero : ({0} : Set (Fin 3))ᶜ = {1, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_8815746.compl_one : ({1} : Set (Fin 3))ᶜ = {0, 2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_8815746.compl_two : ({2} : Set (Fin 3))ᶜ = {0, 1} := by
  ext i; fin_cases i <;> simp

lemma frame_3_8815746.compl_zero_one : ({0, 1} : Set (Fin 3))ᶜ = {2} := by
  ext i; fin_cases i <;> simp

lemma frame_3_8815746.compl_zero_two : ({0, 2} : Set (Fin 3))ᶜ = {1} := by
  ext i; fin_cases i <;> simp

lemma frame_3_8815746.compl_one_two : ({1, 2} : Set (Fin 3))ᶜ = {0} := by
  ext i; fin_cases i <;> simp

lemma frame_3_8815746.dia_empty :
    frame_3_8815746.dia (∅ : Set (Fin 3)) = ∅ := by
  simp [Frame.dia, frame_3_8815746.box_univ]

lemma frame_3_8815746.dia_zero :
    frame_3_8815746.dia ({0} : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_8815746.compl_zero, frame_3_8815746.box_one_two]

lemma frame_3_8815746.dia_one :
    frame_3_8815746.dia ({1} : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_8815746.compl_one, frame_3_8815746.box_zero_two]

lemma frame_3_8815746.dia_two :
    frame_3_8815746.dia ({2} : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_8815746.compl_two, frame_3_8815746.box_zero_one]

lemma frame_3_8815746.dia_zero_one :
    frame_3_8815746.dia ({0, 1} : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_8815746.compl_zero_one, frame_3_8815746.box_two]

lemma frame_3_8815746.dia_zero_two :
    frame_3_8815746.dia ({0, 2} : Set (Fin 3)) = {0} := by
  simp [Frame.dia, frame_3_8815746.compl_zero_two, frame_3_8815746.box_one,
    frame_3_8815746.compl_one_two]

lemma frame_3_8815746.dia_one_two :
    frame_3_8815746.dia ({1, 2} : Set (Fin 3)) = {1} := by
  simp [Frame.dia, frame_3_8815746.compl_one_two, frame_3_8815746.box_zero,
    frame_3_8815746.compl_zero_two]

lemma frame_3_8815746.dia_univ :
    frame_3_8815746.dia (Set.univ : Set (Fin 3)) = Set.univ := by
  simp [Frame.dia, frame_3_8815746.box_empty]

instance : frame_3_8815746.IsSerial := ⟨fun X => by
  by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X
  · have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.box_univ, frame_3_8815746.dia_univ]
  · have hX : X = ({0, 1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.box_zero_one]
  · have hX : X = ({0, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.box_zero_two]
  · have hX : X = ({0} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.box_zero, frame_3_8815746.dia_zero]
  · have hX : X = ({1, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.box_one_two]
  · have hX : X = ({1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.box_one, frame_3_8815746.dia_one]
  · have hX : X = ({2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.box_two]
  · have hX : X = (∅ : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.box_empty]⟩

instance : frame_3_8815746.IsSymmetric := ⟨fun X => by
  by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X
  · have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_univ, frame_3_8815746.box_univ]
  · have hX : X = ({0, 1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_zero_one, frame_3_8815746.box_univ]
  · have hX : X = ({0, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_zero_two, frame_3_8815746.box_zero]
  · have hX : X = ({0} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_zero, frame_3_8815746.box_univ]
  · have hX : X = ({1, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_one_two, frame_3_8815746.box_one]
  · have hX : X = ({1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_one, frame_3_8815746.box_univ]
  · have hX : X = ({2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_two, frame_3_8815746.box_univ]
  · have hX : X = (∅ : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_empty, frame_3_8815746.box_empty]⟩

instance : frame_3_8815746.IsEuclidean := ⟨fun X => by
  by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;> by_cases h2 : (2 : Fin 3) ∈ X
  · have hX : X = Set.univ := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_univ, frame_3_8815746.box_univ]
  · have hX : X = ({0, 1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_zero_one, frame_3_8815746.box_univ]
  · have hX : X = ({0, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_zero_two, frame_3_8815746.box_zero]
  · have hX : X = ({0} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_zero, frame_3_8815746.box_univ]
  · have hX : X = ({1, 2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_one_two, frame_3_8815746.box_one]
  · have hX : X = ({1} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_one, frame_3_8815746.box_univ]
  · have hX : X = ({2} : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_two, frame_3_8815746.box_univ]
  · have hX : X = (∅ : Set (Fin 3)) := by ext i; fin_cases i <;> simp_all
    subst hX; simp [frame_3_8815746.dia_empty, frame_3_8815746.box_empty]⟩

lemma frame_3_8815746.not_isReflexive : ¬frame_3_8815746.IsReflexive := by
  intro hR
  have h2 : (2 : Fin 3) ∈ frame_3_8815746.box ({0} : Set (Fin 3)) := by
    rw [frame_3_8815746.box_zero]; simp
  exact absurd (frame_3_8815746.refl h2) (by simp)

lemma frame_3_8815746.not_valid_axiomT :
    ¬frame_3_8815746 ⊧ (Axioms.T #a : Formula α) :=
  fun h => frame_3_8815746.not_isReflexive (isReflexive_of_valid_axiomT h)

lemma frame_3_8815746.not_isTransitive :
    ¬frame_3_8815746.IsTransitive := by
  intro hT
  have h := hT.trans ({0} : Set (Fin 3))
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq] at h
  rw [frame_3_8815746.box_zero, frame_3_8815746.box_zero_two] at h
  exact absurd (h (show (0 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) by simp)) (by simp)

lemma frame_3_8815746.not_valid_axiomFour :
    ¬frame_3_8815746 ⊧ (Axioms.Four #a : Formula α) :=
  fun h => frame_3_8815746.not_isTransitive (isTransitive_of_valid_axiomFour h)

end
