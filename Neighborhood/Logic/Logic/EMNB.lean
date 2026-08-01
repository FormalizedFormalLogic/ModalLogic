module

public import Neighborhood.Logic.Logic.ENB
public import Neighborhood.Logic.Logic.EMB
public import Neighborhood.Logic.Logic.EMN
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Logic.Logic.EMCB

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMNB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.ContainsUnit]
    [F.IsSymmetric] :
    A ∈ LogicEMNB → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMNB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMNB.sound frame_1_2 hC⟩

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMNB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMNB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMNB α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMNB.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMNB α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMNB.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMNB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFour (LogicEMNB.sound frame_2_140 (hcon #a))

lemma not_provable_axiomFive (a : α) : ∃ A, Axioms.Five A ∉ (@LogicEMNB α) := by
  by_contra! hcon
  exact frame_2_140.not_valid_axiomFive (LogicEMNB.sound frame_2_140 (hcon #a))

end LogicEMNB

/-- The axiom `N` is redundant over `M` and `B`. -/
theorem LogicEMNB.eq_LogicEMB : (@LogicEMNB α) = LogicEMB := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomB
  · exact Hilbert.subset_of_subset_axioms (by grind)

/-- `EMCB` and `EMNB` are the same logic. -/
theorem LogicEMNB.eq_LogicEMCB : (@LogicEMNB α) = LogicEMCB :=
  LogicEMNB.eq_LogicEMB.trans LogicEMCB.eq_LogicEMB.symm

end
