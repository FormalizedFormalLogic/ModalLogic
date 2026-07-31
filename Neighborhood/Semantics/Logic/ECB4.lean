module

public import Neighborhood.Semantics.Logic.ECN4
public import Neighborhood.Semantics.Logic.ECNB
public import Neighborhood.Semantics.Logic.EB4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_138
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_11570344

/-!
# The neighborhood logic `LogicECB4`

Soundness and consistency of `LogicECB4`, the classical modal logic axiomatised by the
regularity axiom `C`, the symmetry axiom `B` and the transitivity axiom `Four`, with respect to
the neighborhood frames that are regular, symmetric and transitive. Also proves the strict
inclusions of `LogicECN4`, `LogicECNB` and `LogicEB4` in `LogicECB4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECB4

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.IsSymmetric] [F.IsTransitive] :
    A ∈ LogicECB4 → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

theorem consistent : (@LogicECB4 α).IsConsistent := by
  by_contra! hC
  simpa using LogicECB4.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECB4 α)) :=
  MaximalConsistentSet.nonempty consistent

end LogicECB4

theorem LogicECN4_ssubset_LogicECB4 : @LogicECN4 ℕ ⊂ LogicECB4 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomN
    · exact Logic.axiomFour
  · intro h
    have hB : Axioms.B #0 ∈ (@LogicECN4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomB (LogicECN4.sound frame_2_138 hB)

theorem LogicECNB_ssubset_LogicECB4 : @LogicECNB ℕ ⊂ LogicECB4 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩)
    · exact Logic.axiomC
    · exact Logic.axiomN
    · exact Logic.axiomB
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicECNB ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomFour (LogicECNB.sound frame_2_140 hFour)

theorem LogicEB4_ssubset_LogicECB4 : @LogicEB4 ℕ ⊂ LogicECB4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ (@LogicEB4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_3_11570344.not_valid_axiomC (LogicEB4.sound frame_3_11570344 hC)

end
