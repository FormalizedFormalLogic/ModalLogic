module

public import Neighborhood.Semantics.Logic.ECN
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_3

/-!
# The neighborhood logic `LogicECND`

Soundness and consistency of `LogicECND`, the classical modal logic axiomatised by the regularity
axiom `C`, `N := □⊤`, and the seriality axiom `D`, with respect to the regular, unit-containing,
and serial neighborhood frames.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicECND.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsRegular] [F.ContainsUnit]
    [F.IsSerial] :
    A ∈ LogicECND → F ⊧ A :=
  Hilbert.sound (by rintro _ ((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) <;> simp)

theorem LogicECND.consistent : (@LogicECND α).IsConsistent := by
  by_contra! hC
  simpa using LogicECND.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicECND α)) :=
  MaximalConsistentSet.nonempty LogicECND.consistent

theorem LogicECN_ssubset_LogicECND : @LogicECN ℕ ⊂ LogicECND := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_left
  · intro h
    have hD : Axioms.D #0 ∈ @LogicECN ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_3.not_valid_axiomD (LogicECN.sound frame_1_3 hD)

end
