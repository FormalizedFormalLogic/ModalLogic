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

abbrev frame_2_72 : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {Set.univ}
    | 1 => {{1}}⟩

instance : frame_2_72.IsReflexive := ⟨by
  intro X x
  match x with
  | 0 => intro hx; simp_all [Frame.box]
  | 1 => intro hx; simp_all [Frame.box]⟩

lemma frame_2_72.box_empty : frame_2_72.box (∅ : Set (Fin 2)) = ∅ := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_72, Set.ext_iff]

lemma frame_2_72.box_zero : frame_2_72.box ({0} : Set (Fin 2)) = ∅ := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_72, Set.ext_iff]

lemma frame_2_72.box_one : frame_2_72.box ({1} : Set (Fin 2)) = {1} := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_72, Set.ext_iff]

lemma frame_2_72.box_univ : frame_2_72.box (Set.univ : Set (Fin 2)) = {0} := by
  ext y; fin_cases y <;> simp [Frame.box, frame_2_72, Set.ext_iff]

instance : frame_2_72.HasPropertyK where
  K X Y w := by
    intro ⟨h1, h2⟩
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl
    · simpa [← Set.Fin2.eq_univ] using h1
    · simp [frame_2_72.box_zero] at h2
    · exfalso
      have hw : w = 1 := by
        have := h2
        rw [frame_2_72.box_one] at this
        exact this
      subst hw
      rw [show ({1}ᶜ : Set (Fin 2)) = {0} from by simp] at h1
      have h1' : (({0} : Set (Fin 2)) ∪ Y) ∈ frame_2_72.𝒩 (1 : Fin 2) := h1
      simp only [Set.mem_singleton_iff] at h1'
      have h0 : (0 : Fin 2) ∈ (({0} : Set (Fin 2)) ∪ Y) := by simp
      rw [h1'] at h0
      simp at h0
    · simp [frame_2_72.box_empty] at h2

lemma frame_2_72.not_valid_axiomM [DecidableEq α] (hab : a ≠ b) :
    ¬frame_2_72 ⊧ (Axioms.M #a #b : Formula α) := fun h => by
  have h0 := h (fun c => if c = a then {1} else if c = b then Set.univ else ∅) 1
  simp [Forces, Frame.box, Set.ext_iff, frame_2_72, Ne.symm hab] at h0

lemma frame_2_72.not_isTransitive : ¬frame_2_72.IsTransitive := fun hT => by
  have h0 : (0 : Fin 2) ∈ frame_2_72.box Set.univ := by simp [Frame.box]
  have h1 := hT.trans Set.univ h0
  simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero, id_eq,
    Frame.box, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.ext_iff] at h1
  have h2 := h1 1
  simp at h2
  have h3 : (0 : Fin 2) ∈ ({1} : Set (Fin 2)) := h2 ▸ Set.mem_univ 0
  simp at h3

end
