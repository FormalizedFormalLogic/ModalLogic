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

abbrev frame_2_8 : Frame (Fin 2) :=
  ⟨fun w => match w with | 0 => ∅ | 1 => {Set.univ}⟩

lemma frame_2_8.not_isTransitive :
    ¬frame_2_8.IsTransitive := by
  intro hC
  have h := hC.trans Set.univ
    (show (1 : Fin 2) ∈ frame_2_8.box Set.univ by simp [Frame.box])
  simp [Frame.box, Set.eq_univ_iff_forall] at h

lemma frame_2_8.not_valid_axiomFour :
    ¬frame_2_8 ⊧ (Axioms.Four #0 : Formula ℕ) :=
  fun h => frame_2_8.not_isTransitive (isTransitive_of_valid_axiomFour h)

instance : frame_2_8.IsRegular where
  regular X Y x hx := by fin_cases x <;> simp_all [Frame.box, frame_2_8]

instance : frame_2_8.IsMonotonic where
  mono X Y x := by fin_cases x <;> simp [Frame.box, frame_2_8]

instance : frame_2_8.IsReflexive where
  refl X x := by fin_cases x <;> simp_all [Frame.box, frame_2_8]

end
