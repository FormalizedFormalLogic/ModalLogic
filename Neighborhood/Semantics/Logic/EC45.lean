module

public import Neighborhood.Semantics.Logic.EC4
public import Neighborhood.Semantics.Logic.EC5
public import Neighborhood.Semantics.Logic.E45

/-!
# The neighborhood logic `LogicEC45`

Soundness and consistency of `LogicEC45`, the classical modal logic axiomatised by the regularity
axiom `C`, the transitivity axiom `Four` and the Euclidean axiom `Five`, with respect to the
regular, transitive and Euclidean neighborhood frames. Also proves the strict inclusion of
`LogicEC4` in `LogicEC45`.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicEC45

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicEC45 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicEC45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEC45.sound frame_1_2 hC⟩

end LogicEC45


theorem LogicEC4_ssubset_LogicEC45 : @LogicEC4 ℕ ⊂ LogicEC45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · obtain ⟨A, hA⟩ := LogicEC4.not_provable_axiomFive (a := (0 : ℕ))
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicEC5_ssubset_LogicEC45 : @LogicEC5 ℕ ⊂ LogicEC45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicEC5.not_provable_axiomFour (a := (0 : ℕ))
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicE45_ssubset_LogicEC45 : @LogicE45 ℕ ⊂ LogicEC45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, B, hA⟩ := LogicE45.not_provable_axiomC (a := (0 : ℕ)) (b := 1) (by simp)
    exact ⟨Axioms.C A B, (ProvableHilbert.axm (by grind)), hA⟩

end
