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

abbrev frame_3_137520 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{1}}
    | 1 => {{0}, {0, 1}}
    | 2 => {{0}, {1, 2}, ∅}⟩

@[simp]
lemma frame_3_137520.not_valid_axiomM :
    ¬frame_3_137520 ⊧ (Axioms.M (.atom 0) (.atom 1) : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0, 1} | 1 => {1, 2} | _ => Set.univ, 0, by
      unfold NotForces Forces; simp [Frame.box, frame_3_137520, Set.ext_iff]; decide⟩

instance : frame_3_137520.IsRegular where
  regular X Y w hw := by
    fin_cases w <;>
      simp only [Frame.box, frame_3_137520, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢ <;>
      grind

end
