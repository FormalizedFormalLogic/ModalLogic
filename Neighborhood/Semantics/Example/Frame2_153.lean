module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}

abbrev frame_2_153 : Frame (Fin 2) := ⟨fun _ => {∅, Set.univ}⟩

@[simp]
lemma frame_2_153.not_valid_axiomM :
    ¬frame_2_153 ⊧ (Axioms.M #0 #1 : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0} | 1 => {1} | _ => Set.univ, 0, by
      unfold NotForces Forces
      simp [Frame.box, frame_2_153, Set.ext_iff]⟩

instance : frame_2_153.IsRegular where
  regular X Y w hw := by
    simp only [Frame.box, frame_2_153, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
    obtain ⟨hX, hY⟩ := hw
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp

instance : frame_2_153.ContainsUnit := ⟨by
  ext w
  simp [Frame.box, frame_2_153]⟩

end
