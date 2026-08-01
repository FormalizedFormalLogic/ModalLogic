module

public import Neighborhood.Semantics.AxiomM
public import Neighborhood.Semantics.AxiomC
public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.AxiomP
public import Neighborhood.Semantics.AxiomK
public import Neighborhood.Semantics.AxiomGeach

@[expose] public section

variable {α : Type u}
variable {a b : α}

abbrev frame_4_11259170869739560 : Frame (Fin 4) := ⟨fun _ => {{0, 1}, {0, 2}}⟩

@[simp]
lemma frame_4_11259170869739560.not_valid_axiomC [DecidableEq α] (hab : a ≠ b) :
    ¬frame_4_11259170869739560 ⊧ (Axioms.C #a #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0, 1} else if c = b then {0, 2} else ∅, 0, by
      unfold NotForces Forces
      simp [Frame.box, frame_4_11259170869739560, Set.ext_iff, Ne.symm hab]⟩

@[simp]
lemma frame_4_11259170869739560.not_valid_axiomM [DecidableEq α] (hab : a ≠ b) :
    ¬frame_4_11259170869739560 ⊧
      (Axioms.M (#a ⋎ #b) #b : Formula α) :=
  Frame.Validate.not_of_exists_valuation_world
    ⟨fun c => if c = a then {0, 1} else if c = b then {0, 2} else ∅, 0, by
      unfold NotForces Forces
      simp [Frame.box, frame_4_11259170869739560, Set.ext_iff, Ne.symm hab]
      decide⟩

instance : frame_4_11259170869739560.NotContainsEmpty := ⟨fun x => by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> · have := Set.ext_iff.mp h 0; simp at this⟩

instance : frame_4_11259170869739560.IsSerial where
  serial X w hw := by
    simp only [Frame.box, frame_4_11259170869739560, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    simp only [Frame.dia, Frame.box, frame_4_11259170869739560, Set.mem_compl_iff,
      Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hw with rfl | rfl <;>
      · rintro (h | h) <;>
        · have h3 := Set.ext_iff.mp h 3
          simp at h3

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
