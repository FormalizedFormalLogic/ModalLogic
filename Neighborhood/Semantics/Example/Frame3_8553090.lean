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

abbrev frame_3_8553090 : Frame (Fin 3) := ⟨fun _ => {{0}, Set.univ}⟩

lemma frame_3_8553090.box_of_not_mem {X : Set (Fin 3)} (h0 : X ≠ {0}) (hu : X ≠ Set.univ) :
    frame_3_8553090.box X = ∅ := by
  ext w
  simp only [Frame.box, frame_3_8553090, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  tauto

lemma frame_3_8553090.box_singleton_zero :
    frame_3_8553090.box ({0} : Set (Fin 3)) = Set.univ := by
  ext w; simp [Frame.box, frame_3_8553090]

instance : frame_3_8553090.NotContainsEmpty := ⟨fun x => by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨(Set.singleton_ne_empty 0).symm, Set.univ_nonempty.ne_empty.symm⟩⟩

instance : frame_3_8553090.ContainsUnit := ⟨by
  ext w; simp [Frame.box, frame_3_8553090]⟩

instance : frame_3_8553090.IsSerial where
  serial X w hw := by
    simp only [Frame.box, frame_3_8553090, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · have hc : ({0} : Set (Fin 3))ᶜ = {1, 2} := by ext i; fin_cases i <;> simp
      have hb : frame_3_8553090.box ({1, 2} : Set (Fin 3)) = ∅ :=
        frame_3_8553090.box_of_not_mem
          (fun h => absurd ((Set.ext_iff.mp h 0).mpr (by simp)) (by simp))
          (fun h => absurd ((Set.ext_iff.mp h 0).mpr (by simp)) (by simp))
      simp [Frame.dia, hc, hb]
    · have hb : frame_3_8553090.box (∅ : Set (Fin 3)) = ∅ :=
        frame_3_8553090.box_of_not_mem
          (fun h => absurd ((Set.ext_iff.mp h 0).mpr (by simp)) (by simp))
          (fun h => absurd ((Set.ext_iff.mp h 0).mpr (by simp)) (by simp))
      simp [Frame.dia, hb]

instance : frame_3_8553090.IsRegular where
  regular X Y w hw := by
    simp only [Frame.box, frame_3_8553090, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
    obtain ⟨hX, hY⟩ := hw
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp

instance : frame_3_8553090.IsTransitive where
  trans X w hw := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    simp only [Frame.box, frame_3_8553090, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · simp [frame_3_8553090.box_singleton_zero, frame_3_8553090.contains_unit]
    · simp [frame_3_8553090.contains_unit]

instance : frame_3_8553090.IsEuclidean :=
  Frame.IsEuclidean.of_alt (fun X a ha => by
    have h : {b : Fin 3 | X ∉ frame_3_8553090.𝒩 b} = Set.univ := by
      ext b; simpa using ha
    rw [h]; simp)

@[simp]
lemma frame_3_8553090.not_valid_axiomK [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_8553090 ⊧ (Axioms.K #a #b : Formula α) := fun h => by
  have h0 := h (fun c => if c = a then {0} else if c = b then {0, 1} else Set.univ) 0
  simp [Forces, Frame.box, Set.ext_iff, Ne.symm hab] at h0
  revert h0
  decide

@[simp]
lemma frame_3_8553090.not_valid_axiomM [DecidableEq α] (hab : a ≠ b) :
    ¬frame_3_8553090 ⊧ (Axioms.M #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0, 1} else if c = b then {0, 2} else Set.univ, 0, by
      unfold NotForces Forces
      simp [Frame.box, frame_3_8553090, Set.ext_iff, Ne.symm hab]
      decide⟩

end
