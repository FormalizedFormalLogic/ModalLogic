module

public import Neighborhood.Semantics.Logic.END
public import Neighborhood.Semantics.Logic.EN4
public import Neighborhood.Semantics.Logic.ED4
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_172

/-!
# The neighborhood logic `LogicEND4`

Soundness and consistency of `LogicEND4`, the classical modal logic axiomatised by `N := □⊤`,
the seriality axiom `D` and the transitivity axiom `Four` over `LogicE`, with respect to the
serial and transitive neighborhood frames containing their unit. Also proves the strict
inclusion of `LogicEND` and of `LogicEN4` in `LogicEND4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEND4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsSerial] [F.IsTransitive] :
    A ∈ LogicEND4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEND4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEND4.sound frame_1_2 hC⟩

end LogicEND4

theorem LogicEND_ssubset_LogicEND4 : @LogicEND ℕ ⊂ LogicEND4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four #0 ∈ @LogicEND ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_172.not_valid_axiomFour
      (LogicEND.sound frame_2_172 hFour)

theorem LogicEN4_ssubset_LogicEND4 : @LogicEN4 ℕ ⊂ LogicEND4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms
      (Set.union_subset_union_left _ Set.subset_union_left)
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEN4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEN4.sound frame_1_3 hD)

theorem LogicED4_ssubset_LogicEND4 : @LogicED4 ℕ ⊂ LogicEND4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ (@LogicED4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicED4.sound frame_1_0 hN)

end
