module

public import Neighborhood.Semantics.Logic.ECND
public import Neighborhood.Semantics.Logic.ECN4
public import Neighborhood.Semantics.Logic.END4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_8431784

/-!
# The neighborhood logic `LogicECND4`

Soundness and consistency of `LogicECND4`, the classical modal logic axiomatised by
the regularity axiom `C`, `N := □⊤`, the seriality axiom `D` and the transitivity axiom `Four`
over `LogicE`, with respect to the regular, unit-containing, serial and transitive neighborhood frames.
Also proves the strict inclusions of `LogicECND`, `LogicECN4` and `LogicEND4` in `LogicECND4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECND4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] [F.IsSerial] [F.IsTransitive] :
    A ∈ LogicECND4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECND4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECND4.sound frame_1_2 hC⟩

end LogicECND4

theorem LogicECND_ssubset_LogicECND4 : @LogicECND ℕ ⊂ LogicECND4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFour : Axioms.Four #0 ∈ @LogicECND ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomFour (LogicECND.sound frame_2_140 hFour)

theorem LogicECN4_ssubset_LogicECND4 : @LogicECN4 ℕ ⊂ LogicECND4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ @LogicECN4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicECN4.sound frame_1_3 hD)

theorem LogicEND4_ssubset_LogicECND4 : @LogicEND4 ℕ ⊂ LogicECND4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicEND4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_8431784.not_valid_axiomC (LogicEND4.sound frame_3_8431784 hC)

end
