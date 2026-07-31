module

public import Neighborhood.Semantics.Logic.EMCN
public import Neighborhood.Semantics.Logic.EMCD
public import Neighborhood.Semantics.Logic.ECND

/-!
# The neighborhood logic `LogicEMCND`

Soundness and consistency of `LogicEMCND`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C`, `N := □⊤`, and the seriality axiom `D`
over `LogicE`, with respect to the neighborhood frames that are monotonic, regular,
contain their unit, and are serial.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCND

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.ContainsUnit] [F.IsSerial] :
    A ∈ LogicEMCND → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCND α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCND.sound frame_1_2 hC⟩

lemma not_provable_axiomB {a : α} : ∃ A, Axioms.B A ∉ (@LogicEMCND α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEMCND.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFive {a : α} : ∃ A, Axioms.Five A ∉ (@LogicEMCND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEMCND.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFour {a : α} : ∃ A, Axioms.Four A ∉ (@LogicEMCND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEMCND.sound frame_2_140 (hcon #a))

lemma not_provable_axiomT {a : α} : ∃ A, Axioms.T A ∉ (@LogicEMCND α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomT (LogicEMCND.sound frame_2_140 (hcon #a))

end LogicEMCND

theorem LogicEMCN_ssubset_LogicEMCND : @LogicEMCN ℕ ⊂ LogicEMCND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEMCN.not_provable_axiomD (a := (0 : ℕ))
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMCD_ssubset_LogicEMCND : @LogicEMCD ℕ ⊂ LogicEMCND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEMCD.not_provable_axiomN⟩

theorem LogicECND_ssubset_LogicEMCND : @LogicECND ℕ ⊂ LogicEMCND := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicECND.not_provable_axiomM (a := (0 : ℕ)) (b := 1) (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
