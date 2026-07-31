module

public import Neighborhood.Semantics.Logic.ECND
public import Neighborhood.Semantics.Logic.ECNB
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_138

/-!
# The neighborhood logic `LogicECNDB`

Soundness and consistency of `LogicECNDB`, the classical modal logic axiomatised by
the regularity axiom `C`, `N := □⊤`, the seriality axiom `D` and the symmetry axiom `B`
over `LogicE`, with respect to the regular, unit-containing, serial and symmetric neighborhood frames.
Also proves the strict inclusions of `LogicECND` and `LogicECNB` in `LogicECNDB`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicECNDB.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] [F.IsSerial] [F.IsSymmetric] :
    A ∈ LogicECNDB → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECNDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECNDB.sound frame_1_2 hC⟩

theorem LogicECND_ssubset_LogicECNDB : @LogicECND ℕ ⊂ LogicECNDB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hB : Axioms.B #0 ∈ @LogicECND ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomB (LogicECND.sound frame_2_138 hB)

theorem LogicECNB_ssubset_LogicECNDB : @LogicECNB ℕ ⊂ LogicECNDB := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ @LogicECNB ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicECNB.sound frame_1_3 hD)

end
