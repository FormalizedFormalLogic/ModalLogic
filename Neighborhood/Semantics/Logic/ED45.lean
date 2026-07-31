module

public import Neighborhood.Semantics.Logic.ED4
public import Neighborhood.Semantics.Logic.E45
public import Neighborhood.Semantics.Logic.ED5

/-!
# The neighborhood logic `LogicED45`

Soundness and consistency of `LogicED45`, the classical modal logic axiomatised by the seriality
axiom `D`, the transitivity axiom `4`, and the euclideanity axiom `5`, with respect to the serial,
transitive, and euclidean neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicED45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSerial] [F.IsTransitive]
    [F.IsEuclidean] :
    A ∈ LogicED45 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicED45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicED45.sound frame_1_2 hC⟩

end LogicED45

theorem LogicED4_ssubset_LogicED45 : @LogicED4 ℕ ⊂ LogicED45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicED4.not_provable_axiomFive (a := (0 : ℕ))
    exact ⟨Axioms.Five A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicE45_ssubset_LogicED45 : @LogicE45 ℕ ⊂ LogicED45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicE45.not_provable_axiomD (a := (0 : ℕ))
    exact ⟨Axioms.D A, (ProvableHilbert.axm (by grind)), hA⟩

theorem LogicED5_ssubset_LogicED45 : @LogicED5 ℕ ⊂ LogicED45 := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · obtain ⟨A, hA⟩ := LogicED5.not_provable_axiomFour (a := (0 : ℕ))
    exact ⟨Axioms.Four A, (ProvableHilbert.axm (by grind)), hA⟩

end
