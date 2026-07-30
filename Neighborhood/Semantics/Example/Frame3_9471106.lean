module

public import Neighborhood.Axioms
public import Neighborhood.Semantics.Basic
public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach
import Mathlib.Tactic.FinCases

@[expose] public section

variable {α : Type u}

abbrev frame_3_9471106 : Frame (Fin 3) := ⟨fun x => {{x}, Set.univ}⟩

instance : frame_3_9471106.ContainsUnit := ⟨by
  ext x
  simp only [Frame.box, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  right; rfl⟩

lemma frame_3_9471106.box_singleton (a : Fin 3) :
    frame_3_9471106.box ({a} : Set (Fin 3)) = {a} := by
  have hne : ({a} : Set (Fin 3)) ≠ Set.univ := by
    obtain ⟨b, hb⟩ := exists_ne a
    intro heq
    exact hb (show b ∈ ({a} : Set (Fin 3)) by rw [heq]; exact Set.mem_univ b)
  ext y
  simp only [Frame.box, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.singleton_eq_singleton_iff]
  constructor
  · rintro (h | h)
    · exact h.symm
    · exact absurd h hne
  · rintro rfl
    left; rfl

instance : frame_3_9471106.IsReflexive := ⟨by
  intro X x hx
  simp only [Frame.box, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · rfl
  · trivial⟩

instance : frame_3_9471106.IsTransitive := ⟨by
  intro X x hx
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
  simp only [Frame.box, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · simp [frame_3_9471106.box_singleton]
  · simp [frame_3_9471106.contains_unit]⟩

lemma frame_3_9471106.not_isEuclidean : ¬frame_3_9471106.IsEuclidean := fun hE => by
  have hdia : frame_3_9471106.dia ({0, 1} : Set (Fin 3)) = {0, 1} := by
    simp only [Set.ext_iff, Frame.dia, Frame.box, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    decide
  have hbox : frame_3_9471106.box ({0, 1} : Set (Fin 3)) = ∅ := by
    simp only [Set.ext_iff, Frame.box, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_empty_iff_false]
    decide
  have h2 := hE.eucl {0, 1}
  rw [hdia, hbox] at h2
  exact (Set.nonempty_of_mem (Set.mem_insert 0 {1})).ne_empty (Set.subset_empty_iff.mp h2)

end
