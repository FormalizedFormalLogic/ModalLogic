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

abbrev Frame.counterframe_axiomC₁ : Frame (Fin 2) :=
  ⟨fun w => match w with
    | 0 => {{0}, {1}, {0, 1}}
    | 1 => {{1}, {0, 1}}⟩

lemma Frame.counterframe_axiomC₁.box_mono {X Y : Set (Fin 2)} (h : X ⊆ Y) :
    Frame.counterframe_axiomC₁.box X ⊆ Frame.counterframe_axiomC₁.box Y := by
  intro w hw
  fin_cases w <;>
    simp only [Frame.box, Frame.counterframe_axiomC₁, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw ⊢ <;>
    rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
    simp_all; grind

@[simp]
lemma Frame.counterframe_axiomC₁.not_valid_axiomC :
    ¬Frame.counterframe_axiomC₁ ⊧ (Axioms.C (.atom 0) (.atom 1) : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0} | 1 => {1} | _ => Set.univ, 0, by
      unfold NotForces Forces; simp [Frame.box, Frame.counterframe_axiomC₁, Set.ext_iff]⟩

instance : Frame.counterframe_axiomC₁.IsMonotonic where
  mono _ _ := Set.subset_inter
    (Frame.counterframe_axiomC₁.box_mono Set.inter_subset_left)
    (Frame.counterframe_axiomC₁.box_mono Set.inter_subset_right)

instance : Frame.counterframe_axiomC₁.ContainsUnit := ⟨by
  rw [Set.Fin2.eq_univ]
  ext w
  fin_cases w <;> simp [Frame.box, Frame.counterframe_axiomC₁]⟩

end
