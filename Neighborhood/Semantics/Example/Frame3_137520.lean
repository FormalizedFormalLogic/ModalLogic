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

abbrev frame_3_137520 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{1}}
    | 1 => {{0}, {0, 1}}
    | 2 => {{0}, {1, 2}, ∅}⟩

@[simp]
lemma frame_3_137520.not_valid_axiomM [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_137520 ⊧ (Axioms.M #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0, 1} else if c = b then {1, 2} else Set.univ, 0, by
      unfold NotForces Forces; simp [Frame.box, frame_3_137520, Set.ext_iff, Ne.symm hab]; decide⟩

instance : frame_3_137520.IsRegular where
  regular X Y w hw := by
    fin_cases w <;>
      simp only [Frame.box, frame_3_137520, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢ <;>
      grind

end
