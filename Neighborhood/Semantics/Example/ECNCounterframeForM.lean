module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}

abbrev Frame.ECN_counterframe_for_M : Frame (Fin 2) := ⟨fun _ => {∅, Set.univ}⟩

@[simp]
lemma Frame.ECN_counterframe_for_M.not_valid_axiomM :
    ¬Frame.ECN_counterframe_for_M ⊧ (Axioms.M (.atom 0) (.atom 1) : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0} | 1 => {1} | _ => Set.univ, 0, by
      unfold NotForces Forces
      simp [Frame.box, Frame.ECN_counterframe_for_M, Set.ext_iff]⟩

instance : Frame.ECN_counterframe_for_M.IsRegular where
  regular X Y w hw := by
    simp only [Frame.box, Frame.ECN_counterframe_for_M, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢
    obtain ⟨hX, hY⟩ := hw
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp

instance : Frame.ECN_counterframe_for_M.ContainsUnit := ⟨by
  ext w
  simp [Frame.box, Frame.ECN_counterframe_for_M]⟩

end
