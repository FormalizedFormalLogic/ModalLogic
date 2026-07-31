module

public import Neighborhood.Semantics.Logic.EN45
public import Neighborhood.Semantics.Logic.EM5
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_153
public import Neighborhood.Semantics.Example.Frame3_10528928

/-!
# The neighborhood logic `LogicEM45`

Soundness and consistency of `LogicEM45`, the classical modal logic axiomatised by the
monotonicity axiom `M`, the transitivity axiom `Four` and the euclidean axiom `Five`, with
respect to the neighborhood frames that are monotonic, transitive and euclidean. Also proves the
strict inclusions of `LogicEN45`, `LogicEMN4` and `LogicEM5` in `LogicEM45`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEM45

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicEM45 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEM45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEM45.sound frame_1_2 hC⟩

end LogicEM45

theorem LogicEN45_ssubset_LogicEM45 : @LogicEN45 ℕ ⊂ LogicEM45 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomN | exact Logic.axiomFour | exact Logic.axiomFive
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicEN45 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_153.not_valid_axiomM (LogicEN45.sound frame_2_153 hM)

theorem LogicEMN4_ssubset_LogicEM45 : @LogicEMN4 ℕ ⊂ LogicEM45 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;>
      first | exact Logic.axiomM | exact Logic.axiomN | exact Logic.axiomFour
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEMN4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomFive
      (Hilbert.sound (F := frame_2_138) (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)
        hFive)

theorem LogicEM5_ssubset_LogicEM45 : @LogicEM5 ℕ ⊂ LogicEM45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicEM5 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_10528928.not_valid_axiomFour (LogicEM5.sound frame_3_10528928 hFour)

end
