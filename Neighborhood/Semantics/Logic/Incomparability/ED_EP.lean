module

public import Neighborhood.Semantics.Logic.EP
public import Neighborhood.Semantics.Logic.ED

/-!
# Incomparability of `LogicED` and `LogicEP`

Neither of the neighborhood logics `LogicED` and `LogicEP` includes the other: the seriality
axiom `D` is a theorem of `LogicED` but not of `LogicEP`, and the possibility axiom `P` is a
theorem of `LogicEP` but not of `LogicED`.
-/

@[expose] public section

theorem LogicED_not_subset_LogicEP : ¬(@LogicED ℕ ⊆ LogicEP) := by
  intro h
  exact LogicEP.not_mem_axiomD (a := 0) (h (ProvableHilbert.axm ⟨_, rfl⟩))

abbrev Frame.trivial_serial_containsEmpty : Frame (Fin 2) :=
  ⟨fun w => match w with | 0 => {∅, {1}} | 1 => {∅, {0}}⟩

instance : Frame.trivial_serial_containsEmpty.IsSerial where
  serial X x := by
    match x with
    | 0 | 1 => rintro (rfl | rfl) <;> simp [Frame.dia, Frame.box]; tauto_set

theorem LogicEP_not_subset_LogicED : ¬(@LogicEP ℕ ⊆ LogicED) := by
  intro h
  have hP : (Axioms.P : Formula ℕ) ∈ LogicED := h (ProvableHilbert.axm rfl)
  have hNCE := notContainsEmpty_of_valid_axiomP
    (LogicED.sound Frame.trivial_serial_containsEmpty hP)
  simpa using hNCE.not_contains_empty (x := 0)

end
