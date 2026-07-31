module

public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.Logic.EN
public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.EP
public import Neighborhood.Semantics.Logic.ENP
public import Neighborhood.Semantics.Example.Frame1_2
public import Neighborhood.Semantics.Example.Frame1_0
public import Neighborhood.Semantics.Example.Frame1_3
public import Neighborhood.Semantics.Example.Frame2_238

/-!
# The neighborhood logic `LogicEND`

Soundness, consistency and completeness of `LogicEND`, the classical modal logic axiomatised by
both `N := □⊤` and the seriality axiom `D` over `LogicE`, with respect to the serial neighborhood
frames containing their unit.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}

theorem LogicEND.sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsSerial] :
    A ∈ LogicEND → F ⊧ A :=
  Hilbert.sound (by rintro _ (rfl | ⟨_, rfl⟩) <;> simp)

theorem LogicEND.consistent : (@LogicEND α).IsConsistent := by
  by_contra! hC
  simpa using LogicEND.sound frame_1_2 hC

instance : Nonempty (MaximalConsistentSet (@LogicEND α)) :=
  MaximalConsistentSet.nonempty LogicEND.consistent

variable [DecidableEq α]

theorem LogicEND.complete
    (h : ∀ {κ : Type u} [Nonempty κ] (F : Frame κ), [F.ContainsUnit] → [F.IsSerial] → F ⊧ A) :
    A ∈ @LogicEND α :=
  (basicCanonicity LogicEND).mem_of_valid
    (h (basicCanonicity LogicEND).toModel.toFrame
      (basicCanonicity LogicEND).toModel.Val)

theorem LogicED_ssubset_LogicEND : @LogicED ℕ ⊂ LogicEND := by
  constructor
  · exact Hilbert.subset_of_subset_axioms Set.subset_union_right
  · intro h
    have hN : (Axioms.N : Formula ℕ) ∈ @LogicED ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_1_0.not_valid_axiomN (LogicED.sound frame_1_0 hN)

instance {κ} [Nonempty κ] {F : Frame κ} [F.ContainsUnit] [F.IsSerial] : F.NotContainsEmpty where
  not_contains_empty x hx := by
    have hbox : x ∈ F.box (∅ : Set κ) := hx
    have hd := F.serial (X := (∅ : Set κ)) hbox
    simp [Frame.dia, F.contains_unit] at hd

theorem LogicENP_ssubset_LogicEND : @LogicENP ℕ ⊂ LogicEND := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro A (rfl | rfl) <;> first | exact Logic.axiomN | exact Logic.axiomP_of_ND
  · intro h
    have hD : Axioms.D #0 ∈ @LogicENP ℕ := h (ProvableHilbert.axm (by grind))
    exact frame_2_238.not_valid_axiomD (LogicENP.sound frame_2_238 hD)

end
