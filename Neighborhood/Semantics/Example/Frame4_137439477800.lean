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

abbrev frame_4_137439477800 : Frame (Fin 4) :=
  ⟨fun w => match w with
    | 0 => {{0, 1}, {0, 2}}
    | 1 => {{0, 1}}
    | 2 => {{0, 2}}
    | 3 => ∅⟩

instance : frame_4_137439477800.HasPropertyK where
  K X Y := by
    rintro w ⟨hw₁, hw₂⟩
    fin_cases w
    · simp only [Frame.box, frame_4_137439477800, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw₁ hw₂
      exfalso
      have h3 : (3 : Fin 4) ∈ Xᶜ ∪ Y := by
        rcases hw₂ with rfl | rfl <;> simp
      rcases hw₁ with h | h <;> rw [h] at h3 <;> simp at h3
    · simp only [Frame.box, frame_4_137439477800, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hw₁ hw₂
      exfalso
      subst hw₂
      have h3 : (3 : Fin 4) ∈ ({0, 1} : Set (Fin 4))ᶜ ∪ Y := by simp
      rw [hw₁] at h3; simp at h3
    · simp only [Frame.box, frame_4_137439477800, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hw₁ hw₂
      exfalso
      subst hw₂
      have h3 : (3 : Fin 4) ∈ ({0, 2} : Set (Fin 4))ᶜ ∪ Y := by simp
      rw [hw₁] at h3; simp at h3
    · simp [Frame.box, frame_4_137439477800] at hw₂

instance : frame_4_137439477800.IsReflexive where
  refl X w hw := by
    fin_cases w
    · simp only [Frame.box, frame_4_137439477800, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl <;> simp
    · simp only [Frame.box, frame_4_137439477800, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hw
      subst hw; simp
    · simp only [Frame.box, frame_4_137439477800, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hw
      subst hw; simp
    · simp [Frame.box, frame_4_137439477800] at hw

lemma frame_4_137439477800.box_zero_one :
    frame_4_137439477800.box ({0, 1} : Set (Fin 4)) = {0, 1} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_137439477800, Set.ext_iff]; decide

lemma frame_4_137439477800.box_zero_two :
    frame_4_137439477800.box ({0, 2} : Set (Fin 4)) = {0, 2} := by
  ext w; fin_cases w <;> simp [Frame.box, frame_4_137439477800, Set.ext_iff]; decide

instance : frame_4_137439477800.IsTransitive where
  trans X := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    intro w hw
    fin_cases w
    · simp only [Frame.box, frame_4_137439477800, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · simp [frame_4_137439477800.box_zero_one]
      · simp [frame_4_137439477800.box_zero_two]
    · simp only [Frame.box, frame_4_137439477800, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hw
      subst hw
      simp [frame_4_137439477800.box_zero_one]
    · simp only [Frame.box, frame_4_137439477800, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hw
      subst hw
      simp [frame_4_137439477800.box_zero_two]
    · simp [Frame.box, frame_4_137439477800] at hw

@[simp]
lemma frame_4_137439477800.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_4_137439477800 ⊧ (Axioms.C #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0, 1} else if c = b then {0, 2} else Set.univ, 0, by
      unfold NotForces Forces
      simp only [Model.truthset.eq_imp, Model.truthset.eq_box,
        Model.truthset.eq_atom, Set.mem_compl_iff, Set.mem_union, not_or, not_not]
      simp [Frame.box, frame_4_137439477800, Ne.symm hab, Set.ext_iff]⟩

end
