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

abbrev frame_1_1 : Frame (Fin 1) := ⟨fun _ => {∅}⟩

instance : frame_1_1.IsRegular := ⟨by
  intro X Y x ⟨hX, hY⟩
  simp only [Frame.box, frame_1_1, Set.mem_setOf_eq, Set.mem_singleton_iff] at hX hY ⊢
  simp [hX, hY]⟩

instance : frame_1_1.IsSerial := ⟨fun X x hx => by simp_all [Frame.dia, Frame.box]⟩

instance : frame_1_1.IsSymmetric := ⟨fun X => by
  rcases Set.Fin1.all_cases X with rfl | rfl <;>
    simp [Frame.dia, Frame.box, Set.Fin1.eq_univ]⟩

@[simp]
lemma frame_1_1.not_valid_axiomN : ¬frame_1_1 ⊧ (Axioms.N : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun _ => ∅, 0, by simp [NotForces, Forces, Frame.box]⟩

lemma frame_1_1.not_isReflexive : ¬frame_1_1.IsReflexive := fun hR => by
  simpa using hR.refl (∅ : Set (Fin 1)) (show (0 : Fin 1) ∈ _ by simp [Frame.box])

@[simp]
lemma frame_1_1.not_valid_axiomP : ¬frame_1_1 ⊧ (Axioms.P : Formula ℕ) := fun h => by
  simpa using (notContainsEmpty_of_valid_axiomP h).not_contains_empty (x := 0)

end
