module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}

abbrev Frame.EK_counterframe_for_M_and_C : Frame (Fin 4) := ⟨fun _ => {{0, 1}, {0, 2}}⟩

@[simp]
lemma Frame.EK_counterframe_for_M_and_C.not_valid_axiomC :
    ¬Frame.EK_counterframe_for_M_and_C ⊧ (Axioms.C (.atom 0) (.atom 1) : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0, 1} | 1 => {0, 2} | _ => ∅, 0, by
      unfold NotForces Forces
      simp [Frame.box, Frame.EK_counterframe_for_M_and_C, Set.ext_iff]⟩

@[simp]
lemma Frame.EK_counterframe_for_M_and_C.not_valid_axiomM :
    ¬Frame.EK_counterframe_for_M_and_C ⊧
      (Axioms.M ((.atom 0) ⋎ (.atom 1)) (.atom 1) : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0, 1} | 1 => {0, 2} | _ => ∅, 0, by
      unfold NotForces Forces
      simp [Frame.box, Frame.EK_counterframe_for_M_and_C, Set.ext_iff]
      decide⟩

instance : Frame.EK_counterframe_for_M_and_C.HasPropertyK where
  K X Y := by
    rintro w ⟨hw₁, hw₂⟩
    simp only [Frame.box, Frame.EK_counterframe_for_M_and_C, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hw₁ hw₂
    exfalso
    rcases hw₂ with rfl | rfl <;>
      rcases hw₁ with h | h <;>
      · have h3 := Set.ext_iff.mp h 3
        simp at h3

end
