module

public import Neighborhood.Semantics.Logic.END
public import Neighborhood.Semantics.Logic.EN4
import Neighborhood.Semantics.Example.Frame1_2
import Neighborhood.Semantics.Example.Frame2_172

/-!
# The neighborhood logic `LogicEND4`

Soundness and consistency of `LogicEND4`, the classical modal logic axiomatised by `N := □⊤`,
the seriality axiom `D` and the transitivity axiom `Four` over `LogicE`, with respect to the
serial and transitive neighborhood frames containing their unit. Also proves the strict
inclusion of `LogicEND` in `LogicEND4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEND4.sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsSerial] [F.IsTransitive] :
    A ∈ LogicEND4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicEND4.consistent : (@LogicEND4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEND4.sound frame_1_2 hC

theorem LogicEND_ssubset_LogicEND4 : @LogicEND ℕ ⊂ LogicEND4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four #0 ∈ @LogicEND ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_172.not_valid_axiomFour
      (LogicEND.sound frame_2_172 hFour)

end
