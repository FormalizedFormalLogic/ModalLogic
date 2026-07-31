module

public import Neighborhood.Semantics.Logic.EMCN
public import Neighborhood.Semantics.Logic.EM5
public import Neighborhood.Semantics.Logic.ECN5
public import Neighborhood.Semantics.Example.Frame3_10529440

/-!
# The neighborhood logic `LogicEMC5`

Soundness and consistency of `LogicEMC5`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the regularity axiom `C` and the euclideanness axiom `Five`, with respect
to the neighborhood frames that are monotonic, regular and euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMC5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsEuclidean] :
    A ∈ LogicEMC5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMC5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMC5.sound frame_1_2 hC⟩

lemma not_provable_axiomD {a : α} : ∃ A, Axioms.D A ∉ (@LogicEMC5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMC5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomFour {a : α} : ∃ A, Axioms.Four A ∉ (@LogicEMC5 α) := by
  by_contra! hcon
  exact frame_3_10529440.not_valid_axiomFour (LogicEMC5.sound frame_3_10529440 (hcon #a))

end LogicEMC5

theorem LogicEMCN_ssubset_LogicEMC5 : @LogicEMCN ℕ ⊂ LogicEMC5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN
  · obtain ⟨A, hA⟩ := LogicEMCN.not_provable_axiomFive (a := (0 : ℕ))
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEM5_ssubset_LogicEMC5 : @LogicEM5 ℕ ⊂ LogicEMC5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEM5.not_provable_axiomC (a := (0 : ℕ)) (b := 1) (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECN5_ssubset_LogicEMC5 : @LogicECN5 ℕ ⊂ LogicEMC5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomN
    · exact Logic.axiomFive
  · obtain ⟨A, B, hA⟩ := LogicECN5.not_provable_axiomM (a := (0 : ℕ)) (b := 1) (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
