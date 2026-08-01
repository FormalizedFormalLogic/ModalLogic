module

public import Neighborhood.Logic.Logic.EN5
public import Neighborhood.Logic.Logic.EM5
public import Neighborhood.Logic.Logic.EMN
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_170
public import Neighborhood.Semantics.Example.Frame2_206
public import Neighborhood.Semantics.Example.Frame3_10528928

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMN5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.ContainsUnit]
    [F.IsEuclidean] :
    A ∈ LogicEMN5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMN5 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMN5.sound frame_1_2 hC⟩

lemma not_provable_axiomK [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.K A B ∉ (@LogicEMN5 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomK hab (LogicEMN5.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomC [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ∃ A B, Axioms.C A B ∉ (@LogicEMN5 α) := by
  by_contra! hcon
  exact frame_2_206.not_valid_axiomC hab (LogicEMN5.sound frame_2_206 (hcon #a #b))

lemma not_provable_axiomT (a : α) : ∃ A, Axioms.T A ∉ (@LogicEMN5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomT (LogicEMN5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomB (a : α) : ∃ A, Axioms.B A ∉ (@LogicEMN5 α) := by
  by_contra! hcon
  exact frame_2_170.not_valid_axiomB (LogicEMN5.sound frame_2_170 (hcon #a))

lemma not_provable_axiomD (a : α) : ∃ A, Axioms.D A ∉ (@LogicEMN5 α) := by
  by_contra! hcon
  exact frame_1_3.not_valid_axiomD (LogicEMN5.sound frame_1_3 (hcon #a))

lemma not_provable_axiomP : (Axioms.P : Formula α) ∉ (@LogicEMN5 α) := by
  intro hcon
  exact frame_1_3.not_valid_axiomP (LogicEMN5.sound frame_1_3 hcon)

lemma not_provable_axiomFour (a : α) : ∃ A, Axioms.Four A ∉ (@LogicEMN5 α) := by
  by_contra! hcon
  exact frame_3_10528928.not_valid_axiomFour (LogicEMN5.sound frame_3_10528928 (hcon #a))

end LogicEMN5

/-- The axiom `N` is redundant over `M` and `5`. -/
theorem LogicEMN5.eq_LogicEM5 : (@LogicEMN5 α) = LogicEM5 := by
  apply Set.Subset.antisymm
  · apply Hilbert.subset_of_provable_axioms
    rintro A ((⟨B, C, rfl⟩ | rfl) | ⟨B, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomFive | exact Logic.axiomN
  · exact Hilbert.subset_of_subset_axioms (by grind)

end
