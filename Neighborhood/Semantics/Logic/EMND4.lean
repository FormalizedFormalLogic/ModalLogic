module

public import Neighborhood.Semantics.Logic.EMND
public import Neighborhood.Semantics.Logic.EMD4
public import Neighborhood.Semantics.Logic.END4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame3_8421506

/-!
# The neighborhood logic `LogicEMND4`

Soundness and consistency of `LogicEMND4`, the classical modal logic axiomatised by
the monotonicity axiom `M`, `N := □⊤`, the seriality axiom `D` and the transitivity axiom `Four`
over `LogicE`, with respect to the monotonic, unit-containing, serial and transitive neighborhood frames.
Also proves the strict inclusions of `LogicEMND`, `LogicEMD4` and `LogicEND4` in `LogicEMND4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEMND4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsMonotonic]
    [F.ContainsUnit] [F.IsSerial] [F.IsTransitive] :
    A ∈ LogicEMND4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((⟨_, _, rfl⟩ | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEMND4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEMND4.sound frame_1_2 hC⟩

theorem LogicEMND_ssubset_LogicEMND4 : @LogicEMND ℕ ⊂ LogicEMND4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFour : Axioms.Four #0 ∈ @LogicEMND ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomFour (LogicEMND.sound frame_2_140 hFour)

theorem LogicEMD4_ssubset_LogicEMND4 : @LogicEMD4 ℕ ⊂ LogicEMND4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicEMD4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicEMD4.sound frame_1_0 hN)

theorem LogicEND4_ssubset_LogicEMND4 : @LogicEND4 ℕ ⊂ LogicEMND4 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hM : Axioms.M #0 #1 ∈ @LogicEND4 ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_3_8421506.not_valid_axiomM (LogicEND4.sound frame_3_8421506 hM)

end
