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

abbrev frame_2_172 : Frame (Fin 2) := ⟨fun x => {{x}ᶜ, Set.univ}⟩

lemma frame_2_172.not_isTransitive :
    ¬frame_2_172.IsTransitive := by
  intro hC
  have hbox0 : frame_2_172.box ({0} : Set (Fin 2)) = {1} := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_172, Set.ext_iff]
  have hbox1 : frame_2_172.box ({1} : Set (Fin 2)) = {0} := by
    ext y; fin_cases y <;> simp [Frame.box, frame_2_172, Set.ext_iff]
  have hiter : frame_2_172.box^[2] ({0} : Set (Fin 2)) = {0} := by
    show frame_2_172.box (frame_2_172.box {0}) = {0}
    rw [hbox0, hbox1]
  have h1 : (1 : Fin 2) ∈ frame_2_172.box ({0} : Set (Fin 2)) := by
    rw [hbox0]; rfl
  have h2 := hC.trans ({0} : Set (Fin 2)) h1
  rw [hiter] at h2
  simp at h2

lemma frame_2_172.not_valid_axiomFour :
    ¬frame_2_172 ⊧ (Axioms.Four #0 : Formula ℕ) :=
  fun h => frame_2_172.not_isTransitive (isTransitive_of_valid_axiomFour h)

instance : frame_2_172.ContainsUnit := ⟨by
  ext x; fin_cases x <;> simp [Frame.box, frame_2_172]⟩

instance : frame_2_172.IsSerial where
  serial X x hx := by
    simp only [frame_2_172, Frame.box, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> fin_cases x <;>
      simp [Frame.box, Frame.dia, frame_2_172, Set.ext_iff]

end
