module

public import Neighborhood.Semantics.Logic.EB
public import Neighborhood.Semantics.Logic.EN4
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame2_140
public import Neighborhood.Semantics.Example.Frame2_138

/-!
# The neighborhood logic `LogicEB4`

Soundness and consistency of `LogicEB4`, the classical modal logic axiomatised by the symmetry
axiom `B` and the transitivity axiom `Four`, with respect to the neighborhood frames that are
symmetric and transitive. Also proves the strict inclusions of `LogicENB` and `LogicEN4` in
`LogicEB4`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEB4.sound {κ} [Nonempty κ] (F : Frame κ) [F.IsSymmetric] [F.IsTransitive] :
    A ∈ LogicEB4 → F ⊧ A :=
  Hilbert.sound (by rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp)

instance : (@LogicEB4 α).IsConsistent := ⟨by
  by_contra! hC
  simpa using LogicEB4.sound frame_1_2 hC⟩

theorem LogicENB_ssubset_LogicEB4 : @LogicENB ℕ ⊂ LogicEB4 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (rfl | ⟨_, rfl⟩) <;> first | exact Logic.axiomN | exact Logic.axiomB
  · intro h
    have hFour : Axioms.Four #0 ∈ (@LogicENB ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_140.not_valid_axiomFour
      (Hilbert.sound (F := frame_2_140) (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp) hFour)

theorem LogicEN4_ssubset_LogicEB4 : @LogicEN4 ℕ ⊂ LogicEB4 := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ (rfl | ⟨_, rfl⟩) <;> first | exact Logic.axiomN | exact Logic.axiomFour
  · intro h
    have hB : Axioms.B #0 ∈ (@LogicEN4 ℕ) := h (ProvableHilbert.axm (by grind))
    exact frame_2_138.not_valid_axiomB (LogicEN4.sound frame_2_138 hB)

end
