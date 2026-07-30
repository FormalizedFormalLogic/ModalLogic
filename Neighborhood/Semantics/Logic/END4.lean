module

public import Neighborhood.Semantics.Logic.END
public import Neighborhood.Semantics.Logic.EN4
import Mathlib.Tactic.FinCases

/-!
# The neighborhood logic `LogicEND4`

Soundness and consistency of `LogicEND4`, the classical modal logic axiomatised by `N := □⊤`,
the seriality axiom `D` and the transitivity axiom `Four` over `LogicE`, with respect to the
serial and transitive neighborhood frames containing their unit. Also proves the strict
inclusion of `LogicEND` in `LogicEND4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

/-! ### Soundness and consistency -/

/-- `LogicEND4` is sound with respect to every serial and transitive neighborhood frame
containing its unit. -/
theorem LogicEND4.sound (h : A ∈ LogicEND4) {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsSerial] [F.IsTransitive] : F ⊧ A :=
  Hilbert.sound
    (by
      rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩)
      · exact valid_axiomN_of_containsUnit
      · exact valid_axiomD_of_isSerial
      · exact valid_axiomFour_of_isTransitive) h

instance : (@LogicEND4 α).Consistent :=
  Hilbert.consistent_of (F := Frame.simple_blackhole)
    (by
      rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩)
      · exact valid_axiomN_of_containsUnit
      · exact valid_axiomD_of_isSerial
      · exact valid_axiomFour_of_isTransitive)

/-! ### Strict inclusion of `LogicEND` -/

/-- `Frame.trivial_containsUnit` (from the strict inclusion of `LogicEN` in `LogicEN4`) is
serial: its only neighborhoods at any world are the complement of the singleton and the whole
carrier, neither of which is the complement of the other. -/
instance : Frame.trivial_containsUnit.IsSerial where
  serial X x hx := by
    simp only [Frame.trivial_containsUnit, Frame.box, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> fin_cases x <;>
      simp [Frame.box, Frame.dia, Frame.trivial_containsUnit, Set.ext_iff]

theorem LogicEND_ssubset_LogicEND4 : @LogicEND ℕ ⊂ LogicEND4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four (.atom 0) ∈ @LogicEND ℕ := h (ProvableHilbert.axm (Or.inr ⟨_, rfl⟩))
    exact Frame.trivial_containsUnit.not_valid_axiomFour
      (LogicEND.sound hFour Frame.trivial_containsUnit)

end
