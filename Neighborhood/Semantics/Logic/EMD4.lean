module

public import Neighborhood.Semantics.Logic.EM4
public import Neighborhood.Semantics.Logic.ED4
public import Neighborhood.Semantics.Logic.EMD
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_172
public import Neighborhood.Semantics.Example.Frame3_8421506

/-!
# The neighborhood logic `LogicEMD4`

Soundness, consistency and the Nonempty instance for maximal consistent sets of `LogicEMD4`,
the classical modal logic axiomatised by the monotonicity axiom `M`, the seriality axiom `D` and
the transitivity axiom `Four`, with respect to the neighborhood frames that are monotonic,
transitive and serial.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMD4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.IsTransitive] [F.IsSerial] :
    A ∈ LogicEMD4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMD4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMD4.sound frame_1_2 hC⟩

theorem LogicEM4_ssubset_LogicEMD4 : @LogicEM4 ℕ ⊂ LogicEMD4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ (@LogicEM4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEM4.sound frame_1_3 hD)

theorem LogicED4_ssubset_LogicEMD4 : @LogicED4 ℕ ⊂ LogicEMD4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicED4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_8421506.not_valid_axiomM (LogicED4.sound frame_3_8421506 hM)

theorem LogicEMD_ssubset_LogicEMD4 : @LogicEMD ℕ ⊂ LogicEMD4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicEMD ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_172.not_valid_axiomFour (LogicEMD.sound frame_2_172 hFour)

end
