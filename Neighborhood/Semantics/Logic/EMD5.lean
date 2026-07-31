module

public import Neighborhood.Semantics.Logic.END5
public import Neighborhood.Semantics.Logic.EMND
public import Neighborhood.Semantics.Logic.EM5
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame3_8553090
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame1_3

/-!
# The neighborhood logic `LogicEMD5`

Soundness and consistency of `LogicEMD5`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the seriality axiom `D` and the euclidean axiom `Five`, with respect
to the neighborhood frames that are monotonic, serial and euclidean.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMD5

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSerial] [F.IsEuclidean] :
    A ∈ LogicEMD5 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem consistent : (@LogicEMD5 α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMD5.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMD5 α)) :=
  MaximalConsistentSet.nonempty LogicEMD5.consistent

end LogicEMD5

theorem LogicEND5_ssubset_LogicEMD5 : @LogicEND5 ℕ ⊂ LogicEMD5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomD | exact Logic.axiomFive
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicEND5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_8553090.not_valid_axiomM (LogicEND5.sound frame_3_8553090 hM)

theorem LogicEMND_ssubset_LogicEMD5 : @LogicEMND ℕ ⊂ LogicEMD5 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomD
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEMND ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomFive (LogicEMND.sound frame_2_140 hFive)

theorem LogicEM5_ssubset_LogicEMD5 : @LogicEM5 ℕ ⊂ LogicEMD5 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hD : Axioms.D #0 ∈ (@LogicEM5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicEM5.sound frame_1_3 hD)

end
