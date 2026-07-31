module

public import Neighborhood.Semantics.Logic.EMCN
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_138

/-!
# The neighborhood logic `LogicEMB`

Soundness and consistency of `LogicEMB`, the classical modal logic axiomatised by the
monotonicity axiom `M` and the symmetry axiom `B`, with respect to the neighborhood frames that
are both monotonic and symmetric.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMB.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic] [F.IsSymmetric] :
    A ∈ LogicEMB → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp)

theorem LogicEMB.consistent : (@LogicEMB α).IsConsistent := by
  by_contra! hC
  simpa using LogicEMB.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEMB α)) :=
  MaximalConsistentSet.nonempty LogicEMB.consistent

theorem LogicEMCN_ssubset_LogicEMB : @LogicEMCN ℕ ⊂ LogicEMB := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) <;>
      first | exact Logic.axiomM | exact Logic.axiomC | exact Logic.axiomN
  · intro h
    have hB : Axioms.B #0 ∈ (@LogicEMCN ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomB (LogicEMCN.sound frame_2_138 hB)

end
