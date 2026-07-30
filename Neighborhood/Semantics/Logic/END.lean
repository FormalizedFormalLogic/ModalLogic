module

public import Neighborhood.Semantics.AxiomN
public import Neighborhood.Semantics.Logic.ED
public import Neighborhood.Semantics.Logic.EP
import Neighborhood.Semantics.Example.Frame1_2
import Neighborhood.Semantics.Example.Frame1_0

/-!
# The neighborhood logic `LogicEND`

Soundness, consistency and completeness of `LogicEND`, the classical modal logic axiomatised by
both `N := □⊤` and the seriality axiom `D` over `LogicE`, with respect to the serial neighborhood
frames containing their unit. Also its strict inclusions of `LogicED` and `LogicEP`.
-/

@[expose] public section

variable {α : Type u} {A : Formula α}


theorem LogicEND.sound {κ} [Nonempty κ] (F : Frame κ) [F.ContainsUnit]
    [F.IsSerial] :
    A ∈ LogicEND → F ⊧ A :=
  Hilbert.sound
    (fun _ hB => by
      rcases hB with rfl | ⟨_, rfl⟩
      · exact valid_axiomN_of_containsUnit
      · exact valid_axiomD_of_isSerial)

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

theorem LogicEP_ssubset_LogicEND : @LogicEP ℕ ⊂ LogicEND := by
  constructor
  · apply Hilbert.subset_of_provable_axioms
    rintro _ rfl
    exact LogicEND.complete (fun _ _ _ => valid_axiomP_of_notContainsEmpty)
  · intro h
    exact LogicEP.not_mem_axiomD (a := 0) (h (ProvableHilbert.axm (by grind)))

end
