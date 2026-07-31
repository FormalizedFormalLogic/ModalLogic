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

abbrev frame_2_238 : Frame (Fin 2) := ⟨fun _ => {S | S ≠ ∅}⟩

instance : frame_2_238.IsMonotonic := ⟨fun X Y w hw => by
  simp only [Frame.box, Set.mem_setOf_eq, ne_eq] at hw ⊢
  constructor
  · rintro rfl; simp at hw
  · rintro rfl; simp at hw⟩

instance : frame_2_238.ContainsUnit := ⟨by simp [Frame.box]⟩

instance : frame_2_238.NotContainsEmpty := ⟨fun x => by simp [Set.mem_setOf_eq]⟩

lemma frame_2_238.not_isSerial : ¬frame_2_238.IsSerial := by
  intro hS
  have h1 : (0 : Fin 2) ∈ frame_2_238.box {0} := by simp [Frame.box]
  have h2 : (0 : Fin 2) ∉ frame_2_238.dia {0} := by simp [Frame.dia, Frame.box]
  exact h2 (hS.serial {0} h1)

@[simp]
lemma frame_2_238.not_valid_axiomK [DecidableEq α] (hab : a ≠ b) :
    ¬frame_2_238 ⊧ (Axioms.K #a #b : Formula α) := fun h => by
  have h0 := h (fun c => if c = a then {0} else ∅) 0
  simp [Forces, Frame.box, Set.ext_iff, Ne.symm hab] at h0

@[simp]
lemma frame_2_238.not_valid_axiomD : ¬frame_2_238 ⊧ (Axioms.D #a : Formula α) :=
  fun h => frame_2_238.not_isSerial (isSerial_of_valid_axiomD h)

end
