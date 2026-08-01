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

abbrev frame_3_1245183 : Frame (Fin 3) :=
  ⟨fun w => match w with
    | 0 => Set.univ
    | 1 => Set.univ
    | 2 => {{0}, {2}}⟩

lemma frame_3_1245183.box_singleton_two :
    frame_3_1245183.box ({2} : Set (Fin 3)) = Set.univ := by
  ext w; fin_cases w <;> simp [Frame.box, frame_3_1245183]

instance : frame_3_1245183.HasPropertyK where
  K X Y := by
    rintro w ⟨hw₁, hw₂⟩
    fin_cases w
    · simp [Frame.box, frame_3_1245183]
    · simp [Frame.box, frame_3_1245183]
    · simp only [Frame.box, frame_3_1245183, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw₁ hw₂
      exfalso
      have h1 : (1 : Fin 3) ∈ Xᶜ ∪ Y := by
        rcases hw₂ with rfl | rfl <;> simp
      rcases hw₁ with h | h <;> rw [h] at h1 <;> simp at h1

instance : frame_3_1245183.IsEuclidean where
  eucl X := by
    have hdia_subset : frame_3_1245183.dia X ⊆ {2} := by
      intro w hw
      fin_cases w <;> simp_all [Frame.dia, Frame.box, frame_3_1245183]
    rcases Set.subset_singleton_iff_eq.mp hdia_subset with h | h
    · rw [h]; exact Set.empty_subset _
    · rw [h, frame_3_1245183.box_singleton_two]; exact Set.subset_univ _

@[simp]
lemma frame_3_1245183.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_1245183 ⊧ (Axioms.C #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0} else if c = b then {2} else Set.univ, 2, by
      unfold NotForces Forces; simp [Frame.box, frame_3_1245183, Set.ext_iff, Ne.symm hab]⟩

end
