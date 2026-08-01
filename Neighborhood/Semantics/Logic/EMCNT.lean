module

public import Neighborhood.Semantics.Logic.EMCND
public import Neighborhood.Semantics.Example.Frame3_8421512

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMCNT

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

end LogicEMCNT

theorem LogicEMCND_ssubset_LogicEMCNT : @LogicEMCND ℕ ⊂ LogicEMCNT := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN | exact Logic.axiomD
  · obtain ⟨A, hA⟩ := LogicEMCND.not_provable_axiomT (0 : ℕ)
    exact ⟨Axioms.T A, (ProvableHilbert.axm (by grind)), hA⟩

end
