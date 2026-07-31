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
lemma frame_3_8553090.not_valid_axiomM :
    ¬frame_3_8553090 ⊧ (Axioms.M #0 #1 : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0, 1} | 1 => {0, 2} | _ => Set.univ, 0, by
      unfold NotForces Forces
      simp [Frame.box, frame_3_8553090, Set.ext_iff]
      decide⟩

end
