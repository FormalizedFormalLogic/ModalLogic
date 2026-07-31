module

public import Neighborhood.Semantics.Logic.ECD
public import Neighborhood.Semantics.Logic.EC4
public import Neighborhood.Semantics.Logic.ED4
public import Neighborhood.Semantics.Example.Frame1_1
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_43176

/-!
# The neighborhood logic `LogicECD4`

Soundness and consistency of `LogicECD4`, the classical modal logic axiomatised by
the regularity axiom `C`, the seriality axiom `D`, and the transitivity axiom `Four`,
with respect to the neighborhood frames that are regular, serial, and transitive.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicECD4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSerial]
    [F.IsTransitive] :
    A ∈ LogicECD4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem LogicECD4.consistent : (@LogicECD4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicECD4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECD4 α)) :=
  MaximalConsistentSet.nonempty LogicECD4.consistent

theorem LogicECD_ssubset_LogicECD4 : @LogicECD ℕ ⊂ LogicECD4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hFour : Axioms.Four #0 ∈ @LogicECD ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_1.not_valid_axiomFour (LogicECD.sound frame_1_1 hFour)

theorem LogicEC4_ssubset_LogicECD4 : @LogicEC4 ℕ ⊂ LogicECD4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ @LogicEC4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEC4.sound frame_1_3 hD)

theorem LogicED4_ssubset_LogicECD4 : @LogicED4 ℕ ⊂ LogicECD4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicED4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_43176.not_valid_axiomC (LogicED4.sound frame_3_43176 hC)

end
