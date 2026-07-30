module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}

abbrev frame_4_11259170869739560 : Frame (Fin 4) := ⟨fun _ => {{0, 1}, {0, 2}}⟩

@[simp]
lemma frame_4_11259170869739560.not_valid_axiomC :
    ¬frame_4_11259170869739560 ⊧ (Axioms.C #0 #1 : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0, 1} | 1 => {0, 2} | _ => ∅, 0, by
      unfold NotForces Forces
      simp [Frame.box, frame_4_11259170869739560, Set.ext_iff]⟩

@[simp]
lemma frame_4_11259170869739560.not_valid_axiomM :
    ¬frame_4_11259170869739560 ⊧
      (Axioms.M (#0 ⋎ #1) #1 : Formula ℕ) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun a => match a with | 0 => {0, 1} | 1 => {0, 2} | _ => ∅, 0, by
      unfold NotForces Forces
      simp [Frame.box, frame_4_11259170869739560, Set.ext_iff]
      decide⟩

instance : frame_4_11259170869739560.HasPropertyK where
  K X Y := by
    rintro w ⟨hw₁, hw₂⟩
    simp only [Frame.box, frame_4_11259170869739560, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hw₁ hw₂
    exfalso
    rcases hw₂ with rfl | rfl <;>
      rcases hw₁ with h | h <;>
      · have h3 := Set.ext_iff.mp h 3
        simp at h3

end
