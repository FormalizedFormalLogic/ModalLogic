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

abbrev frame_2_206 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {{0}, {1}, {0, 1}}
    | 1 => {{1}, {0, 1}}⟩

instance : frame_2_206.NotContainsEmpty := ⟨fun x => by
  fin_cases x <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] <;>
    and_intros <;>
    first
      | exact (Set.singleton_ne_empty _).symm
      | exact (Set.insert_nonempty _ _).ne_empty.symm⟩

lemma frame_2_206.box_mono {X Y : Set (Fin 2)} (h : X ⊆ Y) :
    frame_2_206.box X ⊆ frame_2_206.box Y := by
  intro w hw
  fin_cases w <;>
    simp only [Frame.box, frame_2_206, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢ <;>
    rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
    simp_all; grind

@[simp]
lemma frame_2_206.not_valid_axiomK [DecidableEq α] (hab : a ≠ b) :
    ¬frame_2_206 ⊧ (Axioms.K #a #b : Formula α) := fun h => by
  have h0 := h (fun c => if c = a then {0} else if c = b then ∅ else Set.univ) 0
  simp [Forces, Frame.box, Set.ext_iff, Ne.symm hab] at h0

@[simp]
lemma frame_2_206.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_2_206 ⊧ (Axioms.C #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0} else if c = b then {1} else Set.univ, 0, by
      unfold NotForces Forces; simp [Frame.box, frame_2_206, Set.ext_iff, Ne.symm hab]⟩

instance : frame_2_206.IsMonotonic where
  mono _ _ := Set.subset_inter
    (frame_2_206.box_mono Set.inter_subset_left)
    (frame_2_206.box_mono Set.inter_subset_right)

instance : frame_2_206.ContainsUnit := ⟨by
  rw [Set.Fin2.eq_univ]
  ext w
  fin_cases w <;> simp [Frame.box, frame_2_206]⟩

instance : frame_2_206.IsEuclidean where
  eucl X := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl
    · have hdia : frame_2_206.dia ({0, 1} : Set (Fin 2)) = Set.univ := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_206, Set.ext_iff]
      have hbox : frame_2_206.box (Set.univ : Set (Fin 2)) = Set.univ := by
        ext y; fin_cases y <;> simp [Frame.box, frame_2_206, Set.ext_iff]
      rw [hdia, hbox]
    · have hdia : frame_2_206.dia ({0} : Set (Fin 2)) = ∅ := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_206, Set.ext_iff]
      rw [hdia]; exact Set.empty_subset _
    · have hdia : frame_2_206.dia ({1} : Set (Fin 2)) = {1} := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_206, Set.ext_iff]
      have hbox : frame_2_206.box ({1} : Set (Fin 2)) = Set.univ := by
        ext y; fin_cases y <;> simp [Frame.box, frame_2_206, Set.ext_iff]
      rw [hdia, hbox]; exact Set.subset_univ _
    · have hdia : frame_2_206.dia (∅ : Set (Fin 2)) = ∅ := by
        ext y; fin_cases y <;> simp [Frame.dia, Frame.box, frame_2_206, Set.ext_iff]
      rw [hdia]; exact Set.empty_subset _

instance : frame_2_206.IsTransitive where
  trans X := by
    intro w hw
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    fin_cases w <;>
      simp only [Frame.box, frame_2_206, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢ <;>
      rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      simp_all [Set.ext_iff]

end
