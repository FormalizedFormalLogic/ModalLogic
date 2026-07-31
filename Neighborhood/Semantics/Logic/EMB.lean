module

public import Neighborhood.Semantics.Logic.EMCN
public import Neighborhood.Semantics.Logic.ECNB
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame3_9472136

/-!
# The neighborhood logic `LogicEMB`

Soundness and consistency of `LogicEMB`, the classical modal logic axiomatised by the
monotonicity axiom `M` and the symmetry axiom `B`, with respect to the neighborhood frames that
are both monotonic and symmetric.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicEMB

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSymmetric] :
    A ∈ LogicEMB → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMB α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMB.sound frame_1_2 hC⟩

end LogicEMB

theorem LogicEMCN_ssubset_LogicEMB : @LogicEMCN ℕ ⊂ LogicEMB := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN
  · intro h
    have hB : Axioms.B #0 ∈ (@LogicEMCN ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomB (LogicEMCN.sound frame_2_138 hB)

theorem LogicECNB_ssubset_LogicEMB : @LogicECNB ℕ ⊂ LogicEMB := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomN
    · exact Logic.axiomB
  · intro h
    have hM : Axioms.M #0 #1 ∈ (@LogicECNB ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_9472136.not_valid_axiomM (LogicECNB.sound frame_3_9472136 hM)

end
