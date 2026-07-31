module

public import Neighborhood.Semantics.Logic.ECN4
public import Neighborhood.Semantics.Logic.ECN5
public import Neighborhood.Semantics.Logic.EC45
public import Neighborhood.Semantics.Logic.EN45

/-!
# The neighborhood logic `LogicECN45`

Soundness and consistency of `LogicECN45`, the classical modal logic axiomatised by the regularity
axiom `C`, `N := □⊤`, the transitivity axiom `Four` and the euclidean axiom `Five`, with respect
to the regular, unit-containing, transitive and euclidean neighborhood frames.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicECN45

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.ContainsUnit]
    [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicECN45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicECN45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECN45.sound frame_1_2 hC⟩

end LogicECN45

theorem LogicECN4_ssubset_LogicECN45 : @LogicECN4 ℕ ⊂ LogicECN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECN4.not_provable_axiomFive (0 : ℕ)
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicECN5_ssubset_LogicECN45 : @LogicECN5 ℕ ⊂ LogicECN45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicECN5.not_provable_axiomFour (0 : ℕ)
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

end
