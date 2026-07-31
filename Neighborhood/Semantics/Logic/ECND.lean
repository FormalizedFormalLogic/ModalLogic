module

public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Logic.ECP
public import Neighborhood.Semantics.Logic.END
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame3_8431784

/-!
# The neighborhood logic `LogicECND`

Soundness and consistency of `LogicECND`, the classical modal logic axiomatised by the regularity
axiom `C`, `N := □⊤`, and the seriality axiom `D`, with respect to the regular, unit-containing,
and serial neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

namespace LogicECND

theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.ContainsUnit]
    [F.IsSerial] :
    A ∈ LogicECND → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicECND α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicECND.sound frame_1_2 hC⟩

end LogicECND

theorem LogicECN_ssubset_LogicECND : @LogicECN ℕ ⊂ LogicECND := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hD : Axioms.D #0 ∈ @LogicECN ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicECN.sound frame_1_3 hD)

theorem LogicECP_ssubset_LogicECND : @LogicECP ℕ ⊂ LogicECND := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (⟨B, C, rfl⟩ | rfl)
    · exact Logic.axiomC
    · exact Logic.axiomP_of_ND
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicECP ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicECP.sound frame_1_0 hN)

theorem LogicEND_ssubset_LogicECND : @LogicEND ℕ ⊂ LogicECND := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hC : Axioms.C #0 #1 ∈ @LogicEND ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_8431784.not_valid_axiomC (LogicEND.sound frame_3_8431784 hC)

end
