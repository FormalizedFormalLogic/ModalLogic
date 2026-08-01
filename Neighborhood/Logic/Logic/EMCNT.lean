module

public import Neighborhood.Logic.Logic.EMCND
public import Neighborhood.Logic.Logic.ENKT
public import Neighborhood.Logic.Logic.ECNT
public import Neighborhood.Logic.Logic.EMCT
public import Neighborhood.Logic.Logic.EMNT
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_8421512

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCNT

/-- Over `EN`, the axioms `M` and `C` derive `K`, and conversely `K` derives `M` and `C`. -/
theorem eq_LogicENKT : (@LogicEMCNT α) = LogicENKT := by
  hilbert_eq_axioms

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsRegular]
    [F.ContainsUnit] [F.IsReflexive] :
    A ∈ LogicEMCNT → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMCNT α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMCNT.sound frame_1_2 hC⟩

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMCNT α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomB (LogicEMCNT.sound frame_2_138 (hcon #a))

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMCNT α) := by
  by_contra! hcon
  exact frame_3_8421512.not_valid_axiomFour (LogicEMCNT.sound frame_3_8421512 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMCNT α) := by
  by_contra! hcon
  exact frame_2_138.not_valid_axiomFive (LogicEMCNT.sound frame_2_138 (hcon #a))

theorem ssubset_LogicEMCND : @LogicEMCND ℕ ⊂ LogicEMCNT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, hA⟩ := LogicEMCND.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

theorem ssubset_LogicECNT : @LogicECNT ℕ ⊂ LogicEMCNT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicECNT.not_provable_axiomM (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.M A B, ProvableHilbert.axm (by grind), hA⟩

theorem ssubset_LogicEMCT : @LogicEMCT ℕ ⊂ LogicEMCNT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · exact ⟨Axioms.N, ProvableHilbert.axm (by grind), LogicEMCT.not_provable_axiomN⟩

theorem ssubset_LogicEMNT : @LogicEMNT ℕ ⊂ LogicEMCNT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · hilbert_subset_axioms
  · obtain ⟨A, B, hA⟩ := LogicEMNT.not_provable_axiomC (0 : ℕ) 1 (by simp)
    exact ⟨Axioms.C A B, ProvableHilbert.axm (by grind), hA⟩

end LogicEMCNT

end
