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

abbrev frame_3_130 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0}, {0, 1, 2}}
    | 1 => ∅
    | 2 => ∅⟩

instance : frame_3_130.IsReflexive := ⟨fun X w hw => by
  simp only [Frame.box, frame_3_130, Set.mem_setOf_eq] at hw
  fin_cases w
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl <;> simp
  · simp at hw
  · simp at hw⟩

instance : frame_3_130.IsSerial := ⟨fun X w hw => by
  simp only [Frame.box, frame_3_130, Set.mem_setOf_eq] at hw
  simp only [Frame.dia, Frame.box, frame_3_130, Set.mem_compl_iff, Set.mem_setOf_eq]
  fin_cases w
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl <;>
      rintro (h | h) <;> (have h0 := Set.ext_iff.mp h 0; simp at h0)
  · simp at hw
  · simp at hw⟩

@[simp]
lemma frame_3_130.not_valid_axiomK [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_130 ⊧ (Axioms.K #a #b : Formula α) := fun h => by
  have h0 := h (fun c => if c = a then {0} else if c = b then {0, 1} else Set.univ) 0
  simp [Forces, Frame.box, Set.ext_iff, Ne.symm hab] at h0
  revert h0
  decide

end
