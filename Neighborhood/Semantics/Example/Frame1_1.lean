module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}
variable {a b : α}

abbrev frame_1_1 : Frame (Fin 1) := ⟨fun _ => {∅}⟩

instance : frame_1_1.HasPropertyK where
  K X Y w := by
    simp only [Frame.box, frame_1_1, Set.mem_setOf_eq]
    rcases Set.Fin1.all_cases X with rfl | rfl
    · simp [Set.Fin1.eq_univ]
    · simp

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
lemma frame_1_1.not_valid_axiomP : ¬frame_1_1 ⊧ (Axioms.P : Formula α) := fun h => by
  simpa using (notContainsEmpty_of_valid_axiomP h).not_contains_empty (x := 0)

instance : frame_1_1.IsRegular := ⟨by
  intro X Y; simp [Frame.box, frame_1_1]
  intro x
  rcases Set.Fin1.all_cases X with rfl | rfl <;>
    rcases Set.Fin1.all_cases Y with rfl | rfl <;>
    simp [Set.Fin1.eq_univ]⟩

lemma frame_1_1.not_isTransitive : ¬frame_1_1.IsTransitive := fun hT => by
  have h := hT.trans (∅ : Set (Fin 1))
  have hbox : frame_1_1.box (∅ : Set (Fin 1)) = Set.univ := by
    ext x; simp [Frame.box, frame_1_1]
  have hbox2 : frame_1_1.box (Set.univ : Set (Fin 1)) = ∅ := by
    ext x; simp [Frame.box, frame_1_1]
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, hbox, hbox2] at h
  exact absurd (h (show (0 : Fin 1) ∈ Set.univ by simp)) (by simp)

lemma frame_1_1.not_valid_axiomFour :
    ¬frame_1_1 ⊧ (Axioms.Four #a : Formula α) :=
  fun h => frame_1_1.not_isTransitive (isTransitive_of_valid_axiomFour h)

lemma frame_1_1.not_valid_axiomM [DecidableEq α] (hab : a ≠ b) :
    ¬frame_1_1 ⊧ (Axioms.M #a #b : Formula α) := fun h => by
  have h0 := h (fun c => if c = a then ∅ else if c = b then Set.univ else ∅) 0
  simp [Forces, Frame.box, Set.ext_iff, frame_1_1, Ne.symm hab] at h0

end
