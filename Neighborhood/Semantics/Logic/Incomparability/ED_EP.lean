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
  obtain ⟨A, hA⟩ := LogicEP.not_provable_axiomD (0 : ℕ)
  exact hA (h (ProvableHilbert.axm (by grind)))

theorem LogicEP_not_subset_LogicED : ¬(@LogicEP ℕ ⊆ LogicED) := fun h =>
  LogicED.not_provable_axiomP (h (ProvableHilbert.axm (by grind)))

end
