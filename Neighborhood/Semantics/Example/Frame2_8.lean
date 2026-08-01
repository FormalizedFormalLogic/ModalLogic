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

abbrev frame_2_8 : Frame (Fin 2) :=
  ⟨fun w => match w with | 0 => ∅ | 1 => {Set.univ}⟩

instance : frame_2_8.HasPropertyK where
  K X Y w := by
    intro ⟨h1, h2⟩
    fin_cases w
    · simp [Frame.box, frame_2_8] at h2
    · simp only [Frame.box, frame_2_8, Set.mem_setOf_eq] at h1 h2 ⊢
      have hX : X = Set.univ := by
        by_contra hne
        simp [hne] at h2
      simp [hX] at h1
      exact h1

instance : frame_2_8.NotContainsEmpty := ⟨fun x => by
  fin_cases x
  · simp
  · simp only
    intro h
    have : (0 : Fin 2) ∈ (∅ : Set (Fin 2)) ↔ (0 : Fin 2) ∈ (Set.univ : Set (Fin 2)) := by
      rw [h]
    simp at this⟩

instance : frame_2_8.IsSerial where
  serial X := by
    rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
      intro y hy <;> fin_cases y <;>
        simp_all [Frame.box, Frame.dia, frame_2_8, Set.Fin2.eq_univ, Set.ext_iff]

lemma frame_2_8.not_isTransitive :
    ¬frame_2_8.IsTransitive := by
  intro hC
  have h := hC.trans Set.univ
    (show (1 : Fin 2) ∈ frame_2_8.box Set.univ by simp [Frame.box])
  simp [Frame.box, Set.eq_univ_iff_forall] at h

lemma frame_2_8.not_valid_axiomFour {a : α} : ¬frame_2_8 ⊧ (Axioms.Four #a : Formula α) :=
  fun h => frame_2_8.not_isTransitive (isTransitive_of_valid_axiomFour h)

instance : frame_2_8.IsRegular where
  regular X Y x hx := by fin_cases x <;> simp_all [Frame.box, frame_2_8]

instance : frame_2_8.IsMonotonic where
  mono X Y x := by fin_cases x <;> simp [Frame.box, frame_2_8]

instance : frame_2_8.IsReflexive where
  refl X x := by fin_cases x <;> simp_all [Frame.box, frame_2_8]

end
