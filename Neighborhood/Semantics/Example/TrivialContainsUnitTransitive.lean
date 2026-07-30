module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}

abbrev Frame.trivial_containsUnit_transitive : Frame (Fin 2) := ⟨fun _ => {{(1 : Fin 2)}, Set.univ}⟩

lemma Frame.trivial_containsUnit_transitive.not_isReflexive :
    ¬Frame.trivial_containsUnit_transitive.IsReflexive := by
  intro hR
  have h1 : (0 : Fin 2) ∈ Frame.trivial_containsUnit_transitive.box ({1} : Set (Fin 2)) := by
    simp [Frame.box, Frame.trivial_containsUnit_transitive]
  exact absurd (Frame.trivial_containsUnit_transitive.refl h1) (by simp)

lemma Frame.trivial_containsUnit_transitive.not_valid_axiomT :
    ¬Frame.trivial_containsUnit_transitive ⊧ (Axioms.T (.atom 0) : Formula ℕ) :=
  fun h => Frame.trivial_containsUnit_transitive.not_isReflexive (isReflexive_of_valid_axiomT h)

instance : Frame.trivial_containsUnit_transitive.ContainsUnit := ⟨by
  ext x; simp [Frame.box, Frame.trivial_containsUnit_transitive]⟩

instance : Frame.trivial_containsUnit_transitive.IsTransitive where
  trans X := by
    intro x hx
    simp only [Frame.box, Frame.trivial_containsUnit_transitive, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hbox : Frame.trivial_containsUnit_transitive.box X = Set.univ := by
      ext y
      simp only [Frame.box, Frame.trivial_containsUnit_transitive, Set.mem_setOf_eq,
        Set.mem_univ, iff_true]
      rcases hx with rfl | rfl <;> simp
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, hbox]
    simp [Frame.box, Frame.trivial_containsUnit_transitive]

end
