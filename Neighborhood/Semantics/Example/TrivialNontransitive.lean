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

abbrev Frame.trivial_nontransitive : Frame (Fin 2) :=
  ⟨fun w => match w with | 0 => ∅ | 1 => {Set.univ}⟩

lemma Frame.trivial_nontransitive.not_isTransitive :
    ¬Frame.trivial_nontransitive.IsTransitive := by
  intro hC
  have h := hC.trans Set.univ
    (show (1 : Fin 2) ∈ Frame.trivial_nontransitive.box Set.univ by simp [Frame.box])
  simp [Frame.box, Set.eq_univ_iff_forall] at h

lemma Frame.trivial_nontransitive.not_valid_axiomFour :
    ¬Frame.trivial_nontransitive ⊧ (Axioms.Four (.atom 0) : Formula ℕ) :=
  fun h => Frame.trivial_nontransitive.not_isTransitive (isTransitive_of_valid_axiomFour h)

instance : Frame.trivial_nontransitive.IsRegular where
  regular X Y x hx := by fin_cases x <;> simp_all [Frame.box, Frame.trivial_nontransitive]

instance : Frame.trivial_nontransitive.IsMonotonic where
  mono X Y x := by fin_cases x <;> simp [Frame.box, Frame.trivial_nontransitive]

instance : Frame.trivial_nontransitive.IsReflexive where
  refl X x := by fin_cases x <;> simp_all [Frame.box, Frame.trivial_nontransitive]

end
