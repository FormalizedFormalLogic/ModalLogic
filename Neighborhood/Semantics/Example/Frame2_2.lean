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

abbrev frame_2_2 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {{0}}
    | 1 => ∅⟩

lemma frame_2_2.box_empty : frame_2_2.box (∅ : Set (Fin 2)) = ∅ := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_2]

lemma frame_2_2.box_zero : frame_2_2.box ({0} : Set (Fin 2)) = {0} := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_2]

lemma frame_2_2.box_one : frame_2_2.box ({1} : Set (Fin 2)) = ∅ := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_2]

lemma frame_2_2.box_univ : frame_2_2.box (Set.univ : Set (Fin 2)) = ∅ := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_2, Set.ext_iff]

instance : frame_2_2.HasPropertyK where
  K X Y := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl
    · simp [← Set.Fin2.eq_univ, frame_2_2.box_univ]
    · have hZ : frame_2_2.box (insert (1 : Fin 2) Y) = ∅ := by
        ext w
        fin_cases w <;>
          simp only [Frame.box, frame_2_2, Set.mem_setOf_eq, Set.mem_singleton_iff,
            Set.mem_empty_iff_false, iff_false]
        intro heq
        have h1 : (1 : Fin 2) ∈ insert (1 : Fin 2) Y := Set.mem_insert _ _
        rw [heq] at h1
        simp at h1
      simp [hZ, frame_2_2.box_zero]
    · simp [frame_2_2.box_one]
    · simp [frame_2_2.box_empty]

instance : frame_2_2.IsReflexive where
  refl X := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      simp [← Set.Fin2.eq_univ, frame_2_2.box_univ, frame_2_2.box_zero, frame_2_2.box_one,
        frame_2_2.box_empty]

instance : frame_2_2.IsTransitive where
  trans X := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      simp [← Set.Fin2.eq_univ, frame_2_2.box_univ, frame_2_2.box_zero, frame_2_2.box_one,
        frame_2_2.box_empty]

lemma frame_2_2.not_valid_axiomM [DecidableEq α] (hab : a ≠ b) :
    ¬frame_2_2 ⊧ (Axioms.M #a #b : Formula α) := fun h => by
  have h0 := h (fun c => if c = a then Set.univ else if c = b then {0} else ∅) 0
  simp [Forces, Frame.box, Set.ext_iff, frame_2_2, Ne.symm hab] at h0

end
