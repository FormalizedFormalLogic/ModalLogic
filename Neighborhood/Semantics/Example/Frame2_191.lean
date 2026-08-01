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

abbrev frame_2_191 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {∅, {0}, {1}, Set.univ}
    | 1 => {∅, {0}, Set.univ}⟩

instance : frame_2_191.IsTransitive where
  trans X := by
    intro w hw
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    fin_cases w <;>
      simp only [Frame.box, frame_2_191, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢ <;>
      rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      simp_all [Set.ext_iff]

instance : frame_2_191.IsSymmetric where
  symm X := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      intro w hw <;> fin_cases w <;>
        simp_all [Frame.box, Frame.dia, frame_2_191, Set.Fin2.eq_univ, Set.ext_iff]

instance : frame_2_191.IsRegular where
  regular X Y w hw := by
    fin_cases w <;>
      simp only [Frame.box, frame_2_191, Set.mem_inter_iff, Set.mem_setOf_eq,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
    · obtain ⟨hX, hY⟩ := hw
      rcases hX with rfl | rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl | rfl <;> simp
    · obtain ⟨hX, hY⟩ := hw
      rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> simp

instance : frame_2_191.ContainsUnit := ⟨by
  ext w; fin_cases w <;> simp [Frame.box, frame_2_191]⟩

lemma frame_2_191.not_isEuclidean : ¬frame_2_191.IsEuclidean := by
  intro hE
  have hdia : frame_2_191.dia ({0} : Set (Fin 2)) = {1} := by
    ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_191, Set.ext_iff]
  have hbox : frame_2_191.box ({1} : Set (Fin 2)) = {0} := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_191, Set.ext_iff]
  have h1 : (1 : Fin 2) ∈ frame_2_191.dia ({0} : Set (Fin 2)) := by
    rw [hdia]; rfl
  have h2 := hE.eucl ({0} : Set (Fin 2)) h1
  rw [hdia, hbox] at h2
  simp at h2

lemma frame_2_191.not_valid_axiomFive :
    ¬frame_2_191 ⊧ (Axioms.Five #a : Formula α) :=
  fun h => frame_2_191.not_isEuclidean (isEuclidean_of_valid_axiomFive h)

end
