module

public import Neighborhood.Semantics.Logic.EP
public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Example.Frame2_53

/-!
# Incomparability of `LogicED` and `LogicEP`

Neither of the neighborhood logics `LogicED` and `LogicEP` includes the other: the seriality
axiom `D` is a theorem of `LogicED` but not of `LogicEP`, and the possibility axiom `P` is a
theorem of `LogicEP` but not of `LogicED`.
-/

@[expose] public section

theorem LogicED_not_subset_LogicEP : ¬(@LogicED ℕ ⊆ LogicEP) := by
  intro h
  exact LogicEP.not_mem_axiomD (a := 0) (h (ProvableHilbert.axm (by grind)))

theorem LogicEP_not_subset_LogicED : ¬(@LogicEP ℕ ⊆ LogicED) := by
  intro h
  have hP : (Axioms.P : Formula ℕ) ∈ LogicED := h (ProvableHilbert.axm (by grind))
  have hNCE := notContainsEmpty_of_valid_axiomP
    (LogicED.sound frame_2_53 hP)
  simpa using hNCE.not_contains_empty (x := 0)

end
