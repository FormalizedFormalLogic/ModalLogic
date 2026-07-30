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

abbrev frame_2_206 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {{0}, {1}, {0, 1}}
    | 1 => {{1}, {0, 1}}⟩

lemma frame_2_206.box_mono {X Y : Set (Fin 2)} (h : X ⊆ Y) :
    frame_2_206.box X ⊆ frame_2_206.box Y := by
  intro w hw
  fin_cases w <;>
    simp only [Frame.box, frame_2_206, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢ <;>
    rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
    simp_all; grind

@[simp]
lemma frame_2_206.not_valid_axiomC :
    ¬frame_2_206 ⊧ (Axioms.C (.atom 0) (.atom 1) : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0} | 1 => {1} | _ => Set.univ, 0, by
      unfold NotForces Forces; simp [Frame.box, frame_2_206, Set.ext_iff]⟩

instance : frame_2_206.IsMonotonic where
  mono _ _ := Set.subset_inter
    (frame_2_206.box_mono Set.inter_subset_left)
    (frame_2_206.box_mono Set.inter_subset_right)

instance : frame_2_206.ContainsUnit := ⟨by
  rw [Set.Fin2.eq_univ]
  ext w
  fin_cases w <;> simp [Frame.box, frame_2_206]⟩

end
