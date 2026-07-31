module

public import Neighborhood.Semantics.Logic.EMN
public import Neighborhood.Semantics.Logic.EMP
public import Neighborhood.Semantics.Logic.ENP

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMNP

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.ContainsUnit]
    [F.NotContainsEmpty] :
    A ∈ LogicEMNP → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | rfl) <;> simp)

instance : (@LogicEMNP α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMNP.sound frame_1_2 hC⟩

variable [DecidableEq α]

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.IsMonotonic] → [F.ContainsUnit] →
      [F.NotContainsEmpty] → F ⊧ A) :
    A ∈ @LogicEMNP α :=
  (supplementedBasicCanonicalModel LogicEMNP).mem_of_valid
    (h (supplementedBasicCanonicalModel LogicEMNP).toFrame
      (supplementedBasicCanonicalModel LogicEMNP).Val)

omit [DecidableEq α] in
lemma not_provable_axiomD {a : α} : ∃ A, Axioms.D A ∉ (@LogicEMNP α) := by
  by_contra! hcon
  exact frame_2_238.not_valid_axiomD (LogicEMNP.sound frame_2_238 (hcon #a))

end LogicEMNP

theorem LogicEMP_ssubset_LogicEMNP : @LogicEMP ℕ ⊂ LogicEMNP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by rintro A (⟨B, C, rfl⟩ | rfl) <;> grind)
  · exact ⟨Axioms.N, (ProvableHilbert.axm (by grind)), LogicEMP.not_provable_axiomN⟩

theorem LogicEMN_ssubset_LogicEMNP : @LogicEMN ℕ ⊂ LogicEMNP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · exact ⟨Axioms.P, (ProvableHilbert.axm (by grind)), LogicEMN.not_provable_axiomP⟩

theorem LogicENP_ssubset_LogicEMNP : @LogicENP ℕ ⊂ LogicEMNP := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (Set.union_subset_union_left _ Set.subset_union_right)
  · obtain ⟨A, B, hA⟩ := LogicENP.not_provable_axiomM (a := (0 : ℕ)) (b := 1) (by simp)
    exact ⟨Axioms.M A B, (ProvableHilbert.axm (by grind)), hA⟩

end
