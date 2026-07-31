module

public import Neighborhood.Semantics.Logic.END5
public import Neighborhood.Semantics.Logic.EMND
public import Neighborhood.Semantics.Logic.EM5

/-!
# The neighborhood logic `LogicEMD5`

Soundness and consistency of `LogicEMD5`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the seriality axiom `D` and the euclidean axiom `Five`, with respect
to the neighborhood frames that are monotonic, serial and euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMD5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSerial] [F.IsEuclidean] :
    A ∈ LogicEMD5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMD5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMD5.sound frame_1_2 hC⟩

lemma not_provable_axiomFour {a : α} : ∃ A, Axioms.Four A ∉ (@LogicEMD5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomFour (LogicEMD5.sound frame_3_10528928 (hcon #a))

end LogicEMD5

theorem LogicEND5_ssubset_LogicEMD5 : @LogicEND5 ℕ ⊂ LogicEMD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomFive
  · obtain ⟨A, B, hA⟩ := LogicEND5.not_provable_axiomM (a := (0 : ℕ)) (b := 1) (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMND_ssubset_LogicEMD5 : @LogicEMND ℕ ⊂ LogicEMD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomD
  · obtain ⟨A, hA⟩ := LogicEMND.not_provable_axiomFive (a := (0 : ℕ))
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEM5_ssubset_LogicEMD5 : @LogicEM5 ℕ ⊂ LogicEMD5 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEM5.not_provable_axiomD (a := (0 : ℕ))
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

end
