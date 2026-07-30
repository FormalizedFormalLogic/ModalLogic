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

abbrev frame_3_8421512 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => {{0, 1}, Set.univ}
    | 1 => {Set.univ}
    | 2 => {Set.univ}⟩

instance : frame_3_8421512.ContainsUnit := ⟨by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_8421512]⟩

instance : frame_3_8421512.IsReflexive where
  refl X w hw := by
    fin_cases w <;>
      simp only [Frame.box, frame_3_8421512, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw ⊢ <;>
      rcases hw with rfl | rfl <;> simp

lemma frame_3_8421512.box_zero_one :
    frame_3_8421512.box ({0, 1} : Set (Fin 3)) = {0} := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_8421512, Set.ext_iff] <;> decide

lemma frame_3_8421512.box_singleton_zero :
    frame_3_8421512.box ({0} : Set (Fin 3)) = ∅ := by
  ext w
  fin_cases w <;> simp [Frame.box, frame_3_8421512, Set.ext_iff] <;> decide

lemma frame_3_8421512.not_isTransitive :
    ¬frame_3_8421512.IsTransitive := by
  intro hC
  have h := hC.trans ({0, 1} : Set (Fin 3))
    (show (0 : Fin 3) ∈ frame_3_8421512.box {0, 1} by
      rw [frame_3_8421512.box_zero_one]; rfl)
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq] at h
  rw [frame_3_8421512.box_zero_one, frame_3_8421512.box_singleton_zero] at h
  exact h

lemma frame_3_8421512.not_valid_axiomFour :
    ¬frame_3_8421512 ⊧ (Axioms.Four #0 : Formula ℕ) :=
  fun h => frame_3_8421512.not_isTransitive (isTransitive_of_valid_axiomFour h)

end
