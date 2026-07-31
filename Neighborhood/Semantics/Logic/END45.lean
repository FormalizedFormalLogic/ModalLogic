module

public import Neighborhood.Semantics.Logic.END4
public import Neighborhood.Semantics.Logic.EN45
public import Neighborhood.Semantics.Logic.ED45
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_138

/-!
# The neighborhood logic `LogicEND45`

Soundness and consistency of `LogicEND45`, the classical modal logic axiomatised by `N := □⊤`,
the seriality axiom `D`, the transitivity axiom `Four` and the euclidean axiom `Five`, with
respect to the unit-containing, serial, transitive and euclidean neighborhood frames.
-/

@[expose] public section

variable {α : Type u} [DecidableEq α] {A : Formula α}

namespace LogicEND45

omit [DecidableEq α] in
theorem sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit] [F.IsSerial]
    [F.IsTransitive] [F.IsEuclidean] :
    A ∈ LogicEND45 → F ⊧ A :=
  Hilbert.sound (by rintro _ (((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp)

omit [DecidableEq α] in
instance : (@LogicEND45 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEND45.sound frame_1_2 hC⟩

end LogicEND45

theorem LogicEND4_ssubset_LogicEND45 : @LogicEND4 ℕ ⊂ LogicEND45 := by
  constructor
  · exact Hilbert.subset_of_subset_axioms (by grind)
  · intro h
    have hFive : Axioms.Five #0 ∈ (@LogicEND4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomFive
      (LogicEND4.sound frame_2_138 hFive)

end
