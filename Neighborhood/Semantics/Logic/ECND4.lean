module

public import Neighborhood.Semantics.Logic.ECND
public import Neighborhood.Semantics.Logic.ECN4
public import Neighborhood.Semantics.Logic.END4

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
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECND.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECN4_ssubset_LogicECND4 : @LogicECN4 ℕ ⊂ LogicECND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECN4.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEND4_ssubset_LogicECND4 : @LogicEND4 ℕ ⊂ LogicECND4 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEND4.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
