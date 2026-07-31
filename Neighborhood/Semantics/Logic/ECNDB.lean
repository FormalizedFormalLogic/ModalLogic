module

public import Neighborhood.Semantics.Logic.ECND
public import Neighborhood.Semantics.Logic.ECNB

/-!
# The neighborhood logic `LogicECNDB`

Soundness and consistency of `LogicECNDB`, the classical modal logic axiomatised by
the regularity axiom `C`, `N := □⊤`, the seriality axiom `D` and the symmetry axiom `B`
over `LogicE`, with respect to the regular, unit-containing, serial and symmetric neighborhood frames.
Also proves the strict inclusions of `LogicECND` and `LogicECNB` in `LogicECNDB`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECNDB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular]
    [F.ContainsUnit] [F.IsSerial] [F.IsSymmetric] :
    A ∈ LogicECNDB → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECNDB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECNDB.sound frame_1_2 hC⟩

lemma not_provable_axiomT {a : α} : ∃ A, Axioms.T A ∉ (@LogicECNDB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicECNDB.sound frame_2_140 (hcon #a))

end LogicECNDB

theorem LogicECND_ssubset_LogicECNDB : @LogicECND ℕ ⊂ LogicECNDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECND.not_provable_axiomB (a := (0 : ℕ))
    exact ⟨Axioms.B A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECNB_ssubset_LogicECNDB : @LogicECNB ℕ ⊂ LogicECNDB := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECNB.not_provable_axiomD (a := (0 : ℕ))
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
