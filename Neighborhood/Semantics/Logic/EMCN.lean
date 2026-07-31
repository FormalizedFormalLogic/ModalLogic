module

public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Logic.EMC
public import Neighborhood.Semantics.Logic.EMN
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_138

/-!
# The neighborhood logic `LogicEMCN`

Soundness, consistency and completeness of `LogicEMCN`, the classical modal logic axiomatised by
the monotonicity axiom `M`, the regularity axiom `C` and `N := □⊤`, with respect to the
neighborhood frames that are monotonic, regular, and contain their unit.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCN

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsRegular] [F.ContainsUnit] :
    A ∈ LogicEMCN → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) <;> simp)

instance : (@LogicEMCN α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCN.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.IsRegular] →
      [F.ContainsUnit] → F ⊧ A) :
    A ∈ @LogicEMCN α :=
  (supplementedBasicCanonicalModel LogicEMCN).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMCN).toFrame
      (supplementedBasicCanonicalModel LogicEMCN).Val)

omit [DecidableEq α] in
lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMCN α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEMCN.sound frame_2_138 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMCN α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMCN.sound frame_1_3 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCN α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEMCN.sound frame_2_140 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMCN α) := by
  by_contra! hcon
  exact frame_2_172.not_valid_axiomFour (LogicEMCN.sound frame_2_172 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMCN α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMCN.sound frame_1_3 (hcon #a))

omit [DecidableEq α] in
lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMCN α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMCN.sound frame_1_3 hcon)

end LogicEMCN

theorem LogicECN_ssubset_LogicEMCN : @LogicECN ℕ ⊂ LogicEMCN := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicECN.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEMC_ssubset_LogicEMCN : @LogicEMC ℕ ⊂ LogicEMCN := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEMC.not_provable_axiomN⟩

theorem LogicEMN_ssubset_LogicEMCN : @LogicEMN ℕ ⊂ LogicEMCN := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicEMN.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
