module

public import Neighborhood.Semantics.Logic.ECND
public import Neighborhood.Semantics.Logic.ECN5

/-!
# The neighborhood logic `LogicECND5`

Soundness and consistency of `LogicECND5`, the classical modal logic axiomatised by
the regularity axiom `C`, `N := □⊤`, the seriality axiom `D` and the Euclidean axiom `Five`
over `LogicE`, with respect to the regular, unit-containing, serial and Euclidean neighborhood frames.
Also proves the strict inclusions of `LogicECND` and `LogicECN5` in `LogicECND5`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECND5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] [F.IsSerial] [F.IsEuclidean] :
    A ∈ LogicECND5 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECND5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECND5.sound frame_1_2 hC⟩

end LogicECND5

theorem LogicECND_ssubset_LogicECND5 : @LogicECND ℕ ⊂ LogicECND5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECND.not_provable_axiomFive (a := (0 : ℕ))
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECN5_ssubset_LogicECND5 : @LogicECN5 ℕ ⊂ LogicECND5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECN5.not_provable_axiomD (a := (0 : ℕ))
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
