module

public import Neighborhood.Semantics.Logic.EMC
public import Neighborhood.Semantics.Logic.EMD
public import Neighborhood.Semantics.Logic.ECP
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_140

/-!
# The neighborhood logic `LogicEMCD`

Soundness and consistency of `LogicEMCD`, the classical modal logic axiomatised by the monotonicity
axiom `M`, the regularity axiom `C`, and the seriality axiom `D`, with respect to the monotonic,
regular, and serial neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCD

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.IsSerial] :
    A ∈ LogicEMCD → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCD α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCD.sound frame_1_2 hC⟩

lemma not_provable_axiomN : (Axioms.N : Formula α) ∉ (@LogicEMCD α) := by
  intro hcon
  exact frame_1_0.not_valid_axiomN (LogicEMCD.sound frame_1_0 hcon)

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMCD α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomT (LogicEMCD.sound frame_2_170 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMCD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomB (LogicEMCD.sound frame_1_0 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMCD α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEMCD.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCD α) := by
  by_contra! hcon
  exact frame_1_0.not_valid_axiomFive (LogicEMCD.sound frame_1_0 (hcon #a))

end LogicEMCD

theorem LogicEMC_ssubset_LogicEMCD : @LogicEMC ℕ ⊂ LogicEMCD := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEMC.not_provable_axiomD (0 : ℕ)
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMD_ssubset_LogicEMCD : @LogicEMD ℕ ⊂ LogicEMCD := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.union_subset_union_left _ Set.subset_union_left)
  · obtain ⟨A, B, hA⟩ := LogicEMD.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECP_ssubset_LogicEMCD : @LogicECP ℕ ⊂ LogicEMCD := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, C, rfl⟩ | rfl) <;> first | exact Logic.axiomC | exact Logic.axiomP_of_MD
  · obtain ⟨A, B, hA⟩ := LogicECP.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
